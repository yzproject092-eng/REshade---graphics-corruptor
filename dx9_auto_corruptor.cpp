// DX9 Auto Corruptor v2 — ReShade add-on (.addon64, x64 toolchain)
//
// Автообнаружение:
//   * vertex buffer'ы и shader-resource текстуры ловятся сами в init_resource
//   * stride вершин берётся из bind_vertex_buffers, формат (float3-позиция) определяется эвристикой
//   * портятся только ресурсы, которые удалось залочить; остальные помечаются locked-out
//
// Группы порчи (у каждой переключатель 0/1, "шанс" и "% порчи", всё меняется в рантайме):
//   Textures  — шанс на каждую текстуру, % данных, заполненных шумом
//   Vertices  — шанс на каждый буфер, % вершин, заполненных шумом
//   Viewport  — шанс на каждый SetViewport, дрожание позиции/размера
//   Depth     — шум в clear depth, случайные depth func / write / test, дрожание depth range
//
// При access violation пишет место падения в dx9_corruptor_crash.txt (рядом с exe игры).
// ВАЖНО (ABI): ReShade собран MSVC, add-on — mingw. Функции ImGui, которые возвращают ImVec2 по значению
// (GetContentRegionAvail, CalcTextSize, ...) или принимают его по значению (PlotLines), здесь вызывать нельзя.
// Горячие клавиши: F5 текстуры, F6 вершины, F7 viewport, F8 depth, F9 всё вкл/выкл, F10 новый seed.
//
// Сборка (mingw, x64):
//   x86_64-w64-mingw32-g++ -std=c++17 -O2 -shared -static -Wno-attributes -DImTextureID=ImU64
//     -DIMGUI_DEFINE_MATH_OPERATORS -DIMGUI_DISABLE_OBSOLETE_FUNCTIONS -I<reshade>/include -I<imgui>
//     dx9_auto_corruptor.cpp -o dx9_auto_corruptor.addon64
// MSVC: те же макросы в Preprocessor Definitions, x64, DLL, расширение .addon64.

#define IMGUI_DISABLE_INCLUDE_IMCONFIG_H
#include <imgui.h>
#include <reshade.hpp>

#include <windows.h>
#include <algorithm>
#include <cfloat>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <mutex>
#include <unordered_map>
#include <vector>

using namespace reshade::api;

extern "C" __declspec(dllexport) const char *NAME = "DX9 Auto Corruptor";
extern "C" __declspec(dllexport) const char *DESCRIPTION = "Auto-detects and corrupts textures, vertices, viewport and depth.";

namespace
{
	constexpr uint64_t kExampleHandle = 0x000de100000000fa9ull;

	// ======================= настройки =======================
	struct tex_cfg { bool on = true;  float chance = 30.f; float amount = 5.f; int mode = 2; int per_frame = 8; };
	struct vtx_cfg { bool on = true;  float chance = 50.f; float amount = 5.f; int mode = 0; float strength = 10.f; };
	struct vp_cfg  { bool on = false; float chance = 10.f; float pos = 5.f; float size = 5.f; bool jitter_pos = true; bool jitter_size = true; };
	struct dp_cfg  { bool on = false; float chance = 10.f; bool clear_noise = true; bool func = true; bool write = true; bool test = false; bool range = true; float range_amount = 20.f; };

	tex_cfg g_tc;
	vtx_cfg g_vc;
	vp_cfg g_vp;
	dp_cfg g_dp;

	bool g_enabled = true;
	bool g_auto_reroll = false;
	int g_reroll_frames = 120;
	uint32_t g_seed = 1;
	uint64_t g_frame = 0;
	uint32_t g_rs = 0xC0FFEE;

	uint32_t g_vp_hits = 0, g_dp_hits = 0;      // за текущий кадр
	uint64_t g_vp_total = 0, g_dp_total = 0;
	float g_hist[120] = {};
	int g_hist_pos = 0;

	thread_local bool t_in_hook = false;

	// true между reshade_present и finish_present: в этом окне ReShade сам создаёт свои ресурсы
	// (шрифт оверлея, vertex/index буферы UI, текстуры эффектов) — их портить нельзя
	bool g_reshade_busy = false;

	// ======================= rng =======================
	inline uint32_t hash32(uint32_t x)
	{
		x ^= x >> 16; x *= 0x7feb352dU;
		x ^= x >> 15; x *= 0x846ca68bU;
		x ^= x >> 16;
		return x;
	}
	inline float rnd01(uint32_t &s)
	{
		s = hash32(s + 0x9e3779b9U);
		return (s & 0xFFFFFF) / float(0x1000000);
	}
	inline float frand() { g_rs += uint32_t(g_frame); return rnd01(g_rs); }
	inline bool roll(float pct) { return pct >= 100.f || (pct > 0.f && frand() * 100.f < pct); }
	inline uint32_t fbits(float f) { uint32_t u; std::memcpy(&u, &f, 4); return u; }

	// выбран ли ресурс при текущем seed и шансе
	inline bool pick(uint64_t handle, uint32_t salt, float chance_pct)
	{
		if (chance_pct >= 100.f) return true;
		if (chance_pct <= 0.f) return false;
		const uint32_t h = hash32(uint32_t(handle ^ (handle >> 32)) * 2654435761U ^ g_seed * 0x85ebca6bU ^ salt);
		return (h & 0xFFFFFF) * (100.f / 16777216.f) < chance_pct;
	}

	// подпись настроек: если изменилась — ресурс нужно перепортить
	inline uint32_t sig_of(float a, float b, int c, float d)
	{
		uint32_t s = hash32(g_seed * 31u + fbits(a));
		s = hash32(s ^ fbits(b)); s = hash32(s ^ uint32_t(c)); s = hash32(s ^ fbits(d));
		return s ? s : 1u;
	}

	// ======================= ресурсы =======================
	struct vb_entry
	{
		device *dev = nullptr;
		uint64_t size = 0;
		bool dynamic = false;
		uint32_t stride = 0;
		bool layout_known = false, pos_mode = false;
		float maxabs = 1.0f;
		std::vector<uint8_t> orig;
		bool have_orig = false, unlockable = false;
		uint32_t fails = 0, applied_sig = 0;
		uint64_t last_frame = ~0ull;
	};

	struct tex_entry
	{
		device *dev = nullptr;
		resource_desc desc;
		std::vector<std::vector<uint8_t>> orig;
		bool touched = false, unlockable = false;
		uint32_t fails = 0, applied_sig = 0;
	};

	std::mutex g_mtx;
	std::unordered_map<uint64_t, vb_entry> g_vb;
	std::unordered_map<uint64_t, tex_entry> g_tex;

	// ======================= вершины =======================
	void detect_layout(vb_entry &e, const uint8_t *data, uint64_t size)
	{
		e.layout_known = true;
		e.pos_mode = false;
		const uint64_t count = size / e.stride;
		if (e.stride < 12 || count == 0)
			return;
		const uint64_t n = std::min<uint64_t>(count, 32);
		uint32_t ok = 0;
		float maxabs = 0.0f;
		for (uint64_t v = 0; v < n; ++v)
		{
			float f[3];
			std::memcpy(f, data + v * e.stride, 12);
			bool good = true;
			for (float x : f)
			{
				if (!std::isfinite(x) || std::fabs(x) > 1e6f) { good = false; break; }
				maxabs = std::max(maxabs, std::fabs(x));
			}
			ok += good;
		}
		e.pos_mode = ok * 4 >= n * 3 && maxabs > 0.0f;
		e.maxabs = std::clamp(maxabs, 0.1f, 10000.0f);
	}

	void corrupt_vertices(vb_entry &e, uint8_t *data, uint64_t size)
	{
		if (e.stride < 4 || e.stride > 256)
			return;
		const uint64_t count = size / e.stride;
		if (!count)
			return;
		if (!e.layout_known)
			detect_layout(e, data, size);

		// mode: 0 Auto, 1 Position jitter, 2 Position replace, 3 Random bytes (fill with noise)
		int m = g_vc.mode == 0 ? (e.pos_mode ? 1 : 3) : g_vc.mode;
		if ((m == 1 || m == 2) && !e.pos_mode)
			m = 3;
		const float mag = e.maxabs * g_vc.strength / 100.0f;

		for (uint64_t v = 0; v < count; ++v)
		{
			uint32_t s = hash32(g_seed * 2654435761U ^ uint32_t(v));
			if (rnd01(s) * 100.0f >= g_vc.amount)
				continue;
			uint8_t *p = data + v * e.stride;
			if (m == 1 || m == 2)
			{
				for (int k = 0; k < 3; ++k)
				{
					float f;
					std::memcpy(&f, p + k * 4, 4);
					f = (m == 1) ? f + (rnd01(s) - 0.5f) * 2.0f * mag : (rnd01(s) * 2.0f - 1.0f) * e.maxabs;
					if (std::isfinite(f))
						std::memcpy(p + k * 4, &f, 4);
				}
				if (g_vc.mode == 0 && e.stride >= 16 && rnd01(s) < 0.3f) // нормаль/uv/цвет
				{
					const uint32_t words = (e.stride - 12) / 4;
					uint8_t *w = p + 12 + 4 * (uint32_t(rnd01(s) * words) % words);
					uint32_t val;
					std::memcpy(&val, w, 4);
					val ^= 1u << (uint32_t(rnd01(s) * 23.0f) % 23);
					std::memcpy(w, &val, 4);
				}
			}
			else
			{
				for (uint32_t o = 0; o + 4 <= e.stride; o += 4)
				{
					const uint32_t r = hash32(s + o);
					std::memcpy(p + o, &r, 4);
				}
			}
		}
	}

	bool apply_vb(vb_entry &e, resource res, bool restore)
	{
		void *ptr = nullptr;
		if (!e.dev->map_buffer_region(res, 0, UINT64_MAX, map_access::read_write, &ptr) || ptr == nullptr)
		{
			if (++e.fails > 8)
				e.unlockable = true;
			return false;
		}
		uint8_t *data = static_cast<uint8_t *>(ptr);
		if (restore)
		{
			if (e.have_orig)
				std::memcpy(data, e.orig.data(), std::min<uint64_t>(e.orig.size(), e.size));
		}
		else if (e.dynamic)
		{
			corrupt_vertices(e, data, e.size);
		}
		else
		{
			if (!e.have_orig) { e.orig.assign(data, data + e.size); e.have_orig = true; }
			else std::memcpy(data, e.orig.data(), e.size);
			corrupt_vertices(e, data, e.size);
		}
		e.dev->unmap_buffer_region(res);
		return true;
	}

	// ======================= текстуры =======================
	void corrupt_tex_bytes(uint8_t *data, size_t bytes, uint32_t salt)
	{
		const size_t nblocks = bytes / 16;
		if (!nblocks)
			return;
		uint32_t s = hash32(g_seed ^ salt);
		const bool all = g_tc.amount >= 99.9f;
		const size_t ops = all ? nblocks : std::max<size_t>(1, size_t(double(nblocks) * g_tc.amount / 100.0));

		for (size_t i = 0; i < ops; ++i)
		{
			const size_t b = all ? i : std::min(nblocks - 1, size_t(rnd01(s) * float(nblocks)));
			uint8_t *dst = data + b * 16;
			// mode: 0 noise, 1 block copy, 2 mixed
			const bool noise = g_tc.mode == 0 || (g_tc.mode == 2 && rnd01(s) < 0.5f);
			if (noise)
			{
				uint32_t w[4];
				for (auto &x : w) x = hash32(s += 0x632be5abU);
				std::memcpy(dst, w, 16);
			}
			else
			{
				const size_t src = std::min(nblocks - 1, size_t(rnd01(s) * float(nblocks)));
				uint8_t tmp[16];
				std::memcpy(tmp, data + src * 16, 16);
				std::memcpy(dst, tmp, 16);
			}
		}
	}

	bool apply_tex(tex_entry &t, resource res, bool restore)
	{
		const uint32_t levels = std::max<uint32_t>(1, t.desc.texture.levels);
		if (t.orig.size() != levels)
			t.orig.assign(levels, {});
		bool any = false;

		for (uint32_t m = 0; m < levels; ++m)
		{
			subresource_data sub = {};
			if (!t.dev->map_texture_region(res, m, nullptr, map_access::read_write, &sub) || !sub.data || !sub.row_pitch)
				continue;
			const uint32_t h = std::max<uint32_t>(1, t.desc.texture.height >> m);
			const size_t bytes = format_slice_pitch(t.desc.texture.format, sub.row_pitch, h);
			uint8_t *data = static_cast<uint8_t *>(sub.data);

			if (restore)
			{
				if (t.orig[m].size() == bytes)
					std::memcpy(data, t.orig[m].data(), bytes);
			}
			else
			{
				if (t.orig[m].size() != bytes) t.orig[m].assign(data, data + bytes);
				else std::memcpy(data, t.orig[m].data(), bytes);
				corrupt_tex_bytes(data, bytes, m * 7919u + uint32_t(res.handle));
				t.touched = true;
			}
			t.dev->unmap_texture_region(res, m);
			any = true;
		}

		if (!any && ++t.fails >= 2)
			t.unlockable = true;
		return any;
	}

	// ======================= события: ресурсы =======================
	void on_init_resource(device *dev, const resource_desc &desc, const subresource_data *, resource_usage, resource res)
	{
		if (res.handle == kExampleHandle)
			reshade::log::message(reshade::log::level::info, "[corruptor] example resource detected");

		if (g_reshade_busy)
			return; // ресурс создан самим ReShade

		std::lock_guard<std::mutex> lk(g_mtx);
		if (desc.type == resource_type::buffer)
		{
			if ((desc.usage & resource_usage::vertex_buffer) == resource_usage::undefined)
				return;
			vb_entry e;
			e.dev = dev;
			e.size = desc.buffer.size;
			e.dynamic = desc.heap == memory_heap::cpu_to_gpu;
			g_vb[res.handle] = std::move(e);
		}
		else if (desc.type == resource_type::texture_2d)
		{
			if ((desc.usage & (resource_usage::render_target | resource_usage::depth_stencil)) != resource_usage::undefined)
				return;
			if ((desc.usage & resource_usage::shader_resource) == resource_usage::undefined)
				return;
			if (desc.texture.width < 8 || desc.texture.height < 8 || desc.texture.width * uint64_t(desc.texture.height) > 4096ull * 4096ull)
				return;
			tex_entry t;
			t.dev = dev;
			t.desc = desc;
			g_tex[res.handle] = std::move(t);
		}
	}

	void on_destroy_resource(device *, resource res)
	{
		std::lock_guard<std::mutex> lk(g_mtx);
		g_vb.erase(res.handle);
		g_tex.erase(res.handle);
	}

	void on_bind_vertex_buffers(command_list *, uint32_t, uint32_t count, const resource *buffers,
		const uint64_t *, const uint32_t *strides)
	{
		std::lock_guard<std::mutex> lk(g_mtx);
		const uint32_t sig = sig_of(g_vc.chance, g_vc.amount, g_vc.mode, g_vc.strength);
		for (uint32_t i = 0; i < count; ++i)
		{
			auto it = g_vb.find(buffers[i].handle);
			if (it == g_vb.end())
				continue;
			vb_entry &e = it->second;
			if (strides && strides[i])
				e.stride = strides[i];
			if (e.unlockable || e.stride == 0)
				continue;

			const bool sel = g_enabled && g_vc.on && pick(buffers[i].handle, 0x5bd1e995u, g_vc.chance);
			const uint32_t target = sel ? sig : 0;

			if (e.dynamic)
			{
				if (target == 0 || e.last_frame == g_frame)
					continue;
				if (apply_vb(e, buffers[i], false))
				{
					e.applied_sig = target;
					e.last_frame = g_frame;
				}
				continue;
			}
			if (e.applied_sig == target)
				continue;
			if (target == 0 && !e.have_orig) { e.applied_sig = 0; continue; }
			if (apply_vb(e, buffers[i], target == 0))
				e.applied_sig = target;
		}
	}

	// ======================= события: viewport / depth =======================
	void on_bind_viewports(command_list *cmd, uint32_t first, uint32_t count, const viewport *vps)
	{
		if (t_in_hook || !g_enabled || count == 0 || count > 16)
			return;
		const bool do_vp = g_vp.on;
		const bool do_range = g_dp.on && g_dp.range;
		if (!do_vp && !do_range)
			return;

		viewport mod[16];
		bool changed = false;
		for (uint32_t i = 0; i < count; ++i)
		{
			mod[i] = vps[i];
			viewport &v = mod[i];
			if (do_vp && roll(g_vp.chance))
			{
				if (g_vp.jitter_pos)
				{
					v.x = std::max(0.0f, v.x + (frand() - 0.5f) * 2.0f * g_vp.pos / 100.0f * v.width);
					v.y = std::max(0.0f, v.y + (frand() - 0.5f) * 2.0f * g_vp.pos / 100.0f * v.height);
				}
				if (g_vp.jitter_size)
				{
					v.width = std::max(1.0f, v.width * (1.0f + (frand() - 0.5f) * 2.0f * g_vp.size / 100.0f));
					v.height = std::max(1.0f, v.height * (1.0f + (frand() - 0.5f) * 2.0f * g_vp.size / 100.0f));
				}
				changed = true;
				++g_vp_hits;
			}
			if (do_range && roll(g_dp.chance))
			{
				const float a = g_dp.range_amount / 100.0f;
				float lo = std::clamp(v.min_depth + (frand() - 0.5f) * 2.0f * a, 0.0f, 1.0f);
				float hi = std::clamp(v.max_depth + (frand() - 0.5f) * 2.0f * a, 0.0f, 1.0f);
				if (lo > hi) std::swap(lo, hi);
				v.min_depth = lo; v.max_depth = hi;
				changed = true;
				++g_dp_hits;
			}
		}
		if (!changed)
			return;
		t_in_hook = true;
		cmd->bind_viewports(first, count, mod); // перекрывает только что выставленный viewport
		t_in_hook = false;
	}

	bool on_clear_depth_stencil(command_list *cmd, resource_view dsv, const float *depth, const uint8_t *stencil,
		uint32_t rect_count, const rect *rects)
	{
		if (t_in_hook || !g_enabled || !g_dp.on || !g_dp.clear_noise || depth == nullptr || !roll(g_dp.chance))
			return false;
		const float noisy = frand();
		t_in_hook = true;
		cmd->clear_depth_stencil_view(dsv, &noisy, stencil, rect_count, rects);
		t_in_hook = false;
		++g_dp_hits;
		return true; // оригинальный clear пропускаем
	}

	void on_bind_pipeline_states(command_list *cmd, uint32_t count, const dynamic_state *states, const uint32_t *values)
	{
		if (t_in_hook || !g_enabled || !g_dp.on || !(g_dp.func || g_dp.write || g_dp.test) || count == 0 || count > 16)
			return;
		uint32_t nv[16];
		bool changed = false;
		for (uint32_t i = 0; i < count; ++i)
		{
			nv[i] = values[i];
			switch (states[i])
			{
			case dynamic_state::depth_func:
				if (g_dp.func && roll(g_dp.chance)) { nv[i] = uint32_t(frand() * 8.0f) & 7u; changed = true; }
				break;
			case dynamic_state::depth_write_mask:
				if (g_dp.write && roll(g_dp.chance)) { nv[i] = values[i] ? 0u : 1u; changed = true; }
				break;
			case dynamic_state::depth_enable:
				if (g_dp.test && roll(g_dp.chance)) { nv[i] = values[i] ? 0u : 1u; changed = true; }
				break;
			default: break;
			}
		}
		if (!changed)
			return;
		t_in_hook = true;
		cmd->bind_pipeline_states(count, states, nv);
		t_in_hook = false;
		++g_dp_hits;
	}

	// ======================= кадр =======================
	void on_reshade_present(effect_runtime *)
	{
		++g_frame;

		// горячие клавиши
		static bool prev[7] = {};
		const int keys[7] = { VK_F5, VK_F6, VK_F7, VK_F8, VK_F9, VK_F10, 0 };
		bool now[7] = {};
		for (int i = 0; i < 6; ++i) now[i] = (GetAsyncKeyState(keys[i]) & 0x8000) != 0;
		if (now[0] && !prev[0]) g_tc.on = !g_tc.on;
		if (now[1] && !prev[1]) g_vc.on = !g_vc.on;
		if (now[2] && !prev[2]) g_vp.on = !g_vp.on;
		if (now[3] && !prev[3]) g_dp.on = !g_dp.on;
		if (now[4] && !prev[4]) g_enabled = !g_enabled;
		if (now[5] && !prev[5]) ++g_seed;
		std::memcpy(prev, now, sizeof(prev));

		if (g_auto_reroll && g_reroll_frames > 0 && g_frame % uint64_t(g_reroll_frames) == 0)
			++g_seed;

		// история для графика
		g_hist[g_hist_pos] = float(g_vp_hits + g_dp_hits);
		g_hist_pos = (g_hist_pos + 1) % 120;
		g_vp_total += g_vp_hits; g_dp_total += g_dp_hits;
		g_vp_hits = g_dp_hits = 0;

		// текстуры (с бюджетом на кадр, чтобы не было фризов)
		std::lock_guard<std::mutex> lk(g_mtx);
		const uint32_t sig = sig_of(g_tc.chance, g_tc.amount, g_tc.mode, 0.0f);
		int budget = std::max(1, g_tc.per_frame);
		for (auto &[handle, t] : g_tex)
		{
			if (budget <= 0)
				break;
			if (t.unlockable)
				continue;
			const bool sel = g_enabled && g_tc.on && pick(handle, 0x27d4eb2fu, g_tc.chance);
			const uint32_t target = sel ? sig : 0;
			if (t.applied_sig == target)
				continue;
			if (target == 0 && !t.touched) { t.applied_sig = 0; continue; }
			--budget;
			if (apply_tex(t, resource{ handle }, target == 0))
				t.applied_sig = target;
		}
		g_reshade_busy = true; // дальше ReShade рисует эффекты и оверлей
	}

	void on_finish_present(command_queue *, swapchain *)
	{
		g_reshade_busy = false;
	}

	// ======================= лог падений =======================
	// Пишет в dx9_corruptor_crash.txt (рядом с exe игры) модуль и смещение, где случился access violation.
	PVOID g_veh = nullptr;
	LONG g_veh_count = 0;

	void describe_addr(FILE *f, const char *tag, uintptr_t addr)
	{
		HMODULE mod = nullptr;
		char name[MAX_PATH] = "?";
		if (GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT, reinterpret_cast<LPCSTR>(addr), &mod) && mod)
		{
			GetModuleFileNameA(mod, name, MAX_PATH);
			const char *base = std::strrchr(name, '\\');
			std::fprintf(f, "  %s %p  %s + 0x%llx\n", tag, reinterpret_cast<void *>(addr), base ? base + 1 : name,
				(unsigned long long)(addr - reinterpret_cast<uintptr_t>(mod)));
		}
		else
			std::fprintf(f, "  %s %p  (no module)\n", tag, reinterpret_cast<void *>(addr));
	}

	LONG CALLBACK crash_logger(PEXCEPTION_POINTERS ep)
	{
		if (ep->ExceptionRecord->ExceptionCode != EXCEPTION_ACCESS_VIOLATION)
			return EXCEPTION_CONTINUE_SEARCH;
		if (InterlockedIncrement(&g_veh_count) > 8)
			return EXCEPTION_CONTINUE_SEARCH;

		if (FILE *f = std::fopen("dx9_corruptor_crash.txt", "a"))
		{
			std::fprintf(f, "ACCESS VIOLATION frame=%llu seed=%u thread=%lu\n", (unsigned long long)g_frame, g_seed, GetCurrentThreadId());
			const auto &r = *ep->ExceptionRecord;
			std::fprintf(f, "  %s address %p\n", r.ExceptionInformation[0] == 0 ? "read" : (r.ExceptionInformation[0] == 1 ? "write" : "execute"),
				reinterpret_cast<void *>(r.ExceptionInformation[1]));
			describe_addr(f, "RIP", ep->ContextRecord->Rip);
			const uintptr_t *sp = reinterpret_cast<const uintptr_t *>(ep->ContextRecord->Rsp);
			int shown = 0;
			for (int i = 0; i < 256 && shown < 14; ++i)
			{
				HMODULE m = nullptr;
				if (!IsBadReadPtr(sp + i, sizeof(uintptr_t)) &&
					GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT, reinterpret_cast<LPCSTR>(sp[i]), &m) && m)
				{
					describe_addr(f, "stack", sp[i]);
					++shown;
				}
			}
			std::fprintf(f, "\n");
			std::fclose(f);
		}
		return EXCEPTION_CONTINUE_SEARCH;
	}

	// ======================= GUI =======================
	bool toggle_btn(const char *label, bool *v)
	{
		const ImVec4 on(0.13f, 0.58f, 0.27f, 1.0f), on_h(0.18f, 0.72f, 0.34f, 1.0f);
		const ImVec4 off(0.55f, 0.16f, 0.16f, 1.0f), off_h(0.72f, 0.22f, 0.22f, 1.0f);
		ImGui::PushStyleColor(ImGuiCol_Button, *v ? on : off);
		ImGui::PushStyleColor(ImGuiCol_ButtonHovered, *v ? on_h : off_h);
		ImGui::PushStyleColor(ImGuiCol_ButtonActive, *v ? on_h : off_h);
		char buf[128];
		std::snprintf(buf, sizeof(buf), "[%d]  %s  %s###%s", *v ? 1 : 0, label, *v ? "ON" : "OFF", label);
		const bool clicked = ImGui::Button(buf, ImVec2(-FLT_MIN, 30.0f));
		ImGui::PopStyleColor(3);
		if (clicked)
			*v = !*v;
		return clicked;
	}

	void pct_slider(const char *label, float *v, const char *tip = nullptr)
	{
		ImGui::SliderFloat(label, v, 0.0f, 100.0f, "%.1f %%");
		if (tip && ImGui::IsItemHovered())
			ImGui::SetTooltip("%s", tip);
	}

	void preset(float tc, float ta, float vc, float va, bool vp, bool dp, float dpc)
	{
		g_tc.chance = tc; g_tc.amount = ta;
		g_vc.chance = vc; g_vc.amount = va;
		g_vp.on = vp; g_dp.on = dp; g_dp.chance = dpc;
		++g_seed;
	}

	void draw_overlay(effect_runtime *)
	{
		ImGui::TextColored(ImVec4(1.0f, 0.55f, 0.2f, 1.0f), "DX9 AUTO CORRUPTOR");
		ImGui::SameLine();
		ImGui::TextDisabled("seed %u  |  frame %llu", g_seed, (unsigned long long)g_frame);
		toggle_btn("MASTER  (F9)", &g_enabled);

		if (ImGui::BeginTabBar("##corr_tabs"))
		{
			// ---------------- Overview ----------------
			if (ImGui::BeginTabItem("Overview"))
			{
				ImGui::SeparatorText("Presets");
				if (ImGui::Button("Mild", ImVec2(90, 0))) preset(20, 2, 30, 2, false, false, 5);
				ImGui::SameLine();
				if (ImGui::Button("Chaos", ImVec2(90, 0))) preset(50, 15, 60, 10, true, true, 10);
				ImGui::SameLine();
				if (ImGui::Button("Apocalypse", ImVec2(110, 0))) preset(100, 60, 100, 40, true, true, 40);

				ImGui::SeparatorText("Seed");
				if (ImGui::Button("Re-roll seed (F10)", ImVec2(-FLT_MIN, 0)))
					++g_seed;
				ImGui::Checkbox("Auto re-roll", &g_auto_reroll);
				if (g_auto_reroll)
					ImGui::SliderInt("Every N frames", &g_reroll_frames, 1, 600);

				std::lock_guard<std::mutex> lk(g_mtx);
				size_t vb_ok = 0, vb_bad = 0, vb_on = 0, tx_ok = 0, tx_bad = 0, tx_on = 0;
				for (auto &p : g_vb) { (p.second.unlockable ? vb_bad : vb_ok)++; vb_on += p.second.applied_sig != 0 && !p.second.unlockable; }
				for (auto &p : g_tex) { (p.second.unlockable ? tx_bad : tx_ok)++; tx_on += p.second.applied_sig != 0 && !p.second.unlockable; }

				ImGui::SeparatorText("Detected");
				char ov[96];
				std::snprintf(ov, sizeof(ov), "%zu / %zu textures corrupted  (%zu locked-out)", tx_on, tx_ok, tx_bad);
				ImGui::ProgressBar(tx_ok ? float(tx_on) / float(tx_ok) : 0.0f, ImVec2(-FLT_MIN, 0), ov);
				std::snprintf(ov, sizeof(ov), "%zu / %zu vertex buffers corrupted  (%zu locked-out)", vb_on, vb_ok, vb_bad);
				ImGui::ProgressBar(vb_ok ? float(vb_on) / float(vb_ok) : 0.0f, ImVec2(-FLT_MIN, 0), ov);

				ImGui::SeparatorText("Viewport + depth hits");
				float peak = 1.0f, last = g_hist[(g_hist_pos + 119) % 120];
				for (float h : g_hist) peak = std::max(peak, h);
				std::snprintf(ov, sizeof(ov), "last frame: %.0f  (peak %.0f)", last, peak);
				ImGui::ProgressBar(last / peak, ImVec2(-FLT_MIN, 0), ov);
				ImGui::TextDisabled("total: viewport %llu, depth %llu", (unsigned long long)g_vp_total, (unsigned long long)g_dp_total);
				ImGui::EndTabItem();
			}

			// ---------------- Textures ----------------
			if (ImGui::BeginTabItem("Textures"))
			{
				toggle_btn("TEXTURES  (F5)", &g_tc.on);
				ImGui::SeparatorText("How much");
				pct_slider("Chance per texture", &g_tc.chance, "Вероятность, что конкретная текстура будет испорчена при текущем seed");
				pct_slider("Corruption amount", &g_tc.amount, "Сколько процентов данных текстуры заполнить шумом");
				static const char *modes[] = { "White noise", "Block copy", "Mixed" };
				ImGui::Combo("Noise style", &g_tc.mode, modes, 3);
				ImGui::SliderInt("Textures / frame", &g_tc.per_frame, 1, 64);
				ImGui::TextDisabled("Портятся все mip-уровни. Нелокаемые текстуры пропускаются.");
				ImGui::EndTabItem();
			}

			// ---------------- Vertices ----------------
			if (ImGui::BeginTabItem("Vertices"))
			{
				toggle_btn("VERTICES  (F6)", &g_vc.on);
				ImGui::SeparatorText("How much");
				pct_slider("Chance per buffer", &g_vc.chance, "Вероятность, что конкретный vertex buffer будет испорчен при текущем seed");
				pct_slider("Corruption amount", &g_vc.amount, "Сколько процентов вершин в буфере заполнить шумом");
				static const char *modes[] = { "Auto", "Position jitter", "Position replace", "Random bytes" };
				ImGui::Combo("Noise style", &g_vc.mode, modes, 4);
				ImGui::SliderFloat("Jitter strength", &g_vc.strength, 0.1f, 200.0f, "%.1f %% of mesh size", ImGuiSliderFlags_Logarithmic);
				ImGui::TextDisabled("Auto: позиция float3 -> дрожание, иначе случайные байты.");
				ImGui::EndTabItem();
			}

			// ---------------- Viewport ----------------
			if (ImGui::BeginTabItem("Viewport"))
			{
				toggle_btn("VIEWPORT  (F7)", &g_vp.on);
				ImGui::SeparatorText("How much");
				pct_slider("Chance per SetViewport", &g_vp.chance, "Вероятность порчи на каждый вызов установки viewport");
				ImGui::Checkbox("Jitter position", &g_vp.jitter_pos);
				ImGui::SameLine();
				ImGui::Checkbox("Jitter size", &g_vp.jitter_size);
				pct_slider("Position amount", &g_vp.pos, "Максимальное смещение, % от размера viewport");
				pct_slider("Size amount", &g_vp.size, "Максимальное изменение размера, % от размера viewport");
				ImGui::TextDisabled("Если viewport вылезает за render target, драйвер просто игнорирует вызов.");
				ImGui::EndTabItem();
			}

			// ---------------- Depth ----------------
			if (ImGui::BeginTabItem("Depth"))
			{
				toggle_btn("DEPTH BUFFER  (F8)", &g_dp.on);
				ImGui::SeparatorText("How much");
				pct_slider("Chance per event", &g_dp.chance, "Вероятность порчи на каждый clear / смену состояния / viewport");
				ImGui::SeparatorText("What to break");
				ImGui::Checkbox("Noise in depth clear", &g_dp.clear_noise);
				ImGui::Checkbox("Random depth func", &g_dp.func);
				ImGui::Checkbox("Flip depth write", &g_dp.write);
				ImGui::Checkbox("Flip depth test", &g_dp.test);
				ImGui::Checkbox("Jitter depth range (viewport min/max)", &g_dp.range);
				if (g_dp.range)
					pct_slider("Range amount", &g_dp.range_amount);
				ImGui::TextDisabled("Содержимое depth buffer на CPU не лочится, поэтому портятся clear, состояния и range.");
				ImGui::EndTabItem();
			}
			ImGui::EndTabBar();
		}
	}
}

BOOL APIENTRY DllMain(HMODULE hModule, DWORD fdwReason, LPVOID)
{
	switch (fdwReason)
	{
	case DLL_PROCESS_ATTACH:
		if (!reshade::register_addon(hModule))
			return FALSE;
		reshade::register_event<reshade::addon_event::init_resource>(on_init_resource);
		reshade::register_event<reshade::addon_event::destroy_resource>(on_destroy_resource);
		reshade::register_event<reshade::addon_event::bind_vertex_buffers>(on_bind_vertex_buffers);
		reshade::register_event<reshade::addon_event::bind_viewports>(on_bind_viewports);
		reshade::register_event<reshade::addon_event::bind_pipeline_states>(on_bind_pipeline_states);
		reshade::register_event<reshade::addon_event::clear_depth_stencil_view>(on_clear_depth_stencil);
		reshade::register_event<reshade::addon_event::reshade_present>(on_reshade_present);
		reshade::register_event<reshade::addon_event::finish_present>(on_finish_present);
		reshade::register_overlay(nullptr, draw_overlay);
		g_veh = AddVectoredExceptionHandler(1, crash_logger);
		break;
	case DLL_PROCESS_DETACH:
		if (g_veh)
			RemoveVectoredExceptionHandler(g_veh);
		reshade::unregister_addon(hModule);
		break;
	}
	return TRUE;
}
