package game

import "core:c"
import "core:fmt"
import "core:math"
import la "core:math/linalg"
import strings "core:strings"
import rl "vendor:raylib"

Asset :: struct {
	texture_path: string,
	scale:        f32,
	offset:       [2]f32,
}

textures: map[string]rl.Texture

load_texture :: proc(path: string) -> rl.Texture {
	if t, t_ok := textures[path]; t_ok {
		return t
	}

	t := rl.LoadTexture(strings.clone_to_cstring(path, context.temp_allocator))

	rl.GenTextureMipmaps(&t)
	rl.SetTextureFilter(t, .TRILINEAR)
	rl.SetTextureWrap(t, .CLAMP)

	if t.id != 0 {
		textures[path] = t
	}

	return t
}

piston_position_at_crank_angle :: proc(angle: f32, crank_offset: f32, rod_length: f32) -> f32 {
	return(
		crank_offset * math.cos(angle) +
		math.sqrt(
			(rod_length * rod_length) -
			(crank_offset * crank_offset) * (math.sin(angle) * math.sin(angle)),
		) \
	)
}

valve_position_at_angle :: proc(angle: f32, duration: f32, open_angle: f32, lift: f32) -> f32 {
	cycle_angle := math.mod(angle, 4 * math.PI)
	t := math.PI * (cycle_angle - open_angle) / duration
	if cycle_angle >= open_angle && cycle_angle <= open_angle + duration {
		return lift * math.sin(t)
	}
	return 0
}

cylinder_volume_at_crank_angle :: proc(
	angle: f32,
	crank_offset: f32,
	rod_length: f32,
	bore: f32,
	clearance_volume: f32,
) -> f32 {
	tdc_pos := piston_position_at_crank_angle(0, crank_offset, rod_length)
	pos := piston_position_at_crank_angle(angle, crank_offset, rod_length)
	displacement := tdc_pos - pos

	piston_area := math.PI * (bore * bore) / 4.0
	return clearance_volume + piston_area * displacement
}

pressure_at_crank_angle :: proc(
	angle: f32,
	crank_offset: f32,
	rod_length: f32,
	bore: f32,
	clearance_volume: f32,
	p_initial: f32,
	v_initial: f32,
	n: f32,
) -> f32 {
	v := cylinder_volume_at_crank_angle(angle, crank_offset, rod_length, bore, clearance_volume)
	return p_initial * math.pow(v_initial / v, n)
}

wiebe_function :: proc(
	angle: f32,
	a: f32,
	m: f32,
	burn_duration: f32,
	combustion_start: f32,
) -> f32 {
	if angle <= combustion_start do return 0
	z := (angle - combustion_start) / burn_duration
	if z >= 1 do return 1
	return 1 - math.exp(-a * math.pow(z, m + 1))
}

dx_dtheta :: proc(angle: f32, combustion_start_angle: f32, burn_duration: f32) -> f32 {
	n: f32 = 5
	a: f32 = 3
	return(
		(n * a) /
		burn_duration *
		math.pow(((angle - combustion_start_angle) / burn_duration), n - 1) *
		math.exp(-a * math.pow((angle - combustion_start_angle) / burn_duration, n)) \
	)
}

dq_dtheta :: proc(
	angle: f32,
	combustion_start_angle: f32,
	burn_duration: f32,
	Q_total: f32,
) -> f32 {
	if angle < combustion_start_angle || angle > combustion_start_angle + burn_duration {
		return 0
	}
	return Q_total * dx_dtheta(angle, combustion_start_angle, burn_duration)
}

ANGLE_STEPS :: 7200

CycleState :: struct {
	p_trace: [ANGLE_STEPS]f32,
	w_net:   f32,
}

compute_cycle :: proc(
	bore, crank_offset, rod_length, cylinder_height: f32,
	gamma, manifold_pressure, cylinder_temp: f32,
	rpm: f32,
) -> CycleState {
	state: CycleState

	stroke := 2 * crank_offset
	v_swept := (math.PI / 4) * (bore * bore) * stroke
	v_clearance := (math.PI / 4) * (bore * bore) * cylinder_height

	intake_density := 1.225 * (manifold_pressure / 101.325)
	m_air := (v_swept + v_clearance) * 1e-9 * intake_density
	Qin := (m_air / 14.7) * 44_000_000.0

	combustion_start := math.to_radians_f32(355.0)
	burn_duration := math.to_radians_f32(60.0)
	a_wiebe: f32 = 5.0
	m_wiebe: f32 = 2.0
	R_air: f32 = 287.0

	d_theta := (4 * math.PI) / f32(ANGLE_STEPS)
	p := manifold_pressure * 1e3

	for i in 0 ..< ANGLE_STEPS {
		angle := f32(i) * d_theta

		V_cur :=
			cylinder_volume_at_crank_angle(angle, crank_offset, rod_length, bore, v_clearance) *
			1e-9
		V_next :=
			cylinder_volume_at_crank_angle(
				angle + d_theta,
				crank_offset,
				rod_length,
				bore,
				v_clearance,
			) *
			1e-9
		dV := V_next - V_cur

		z_cur := (angle - combustion_start) / burn_duration
		z_next := (angle + d_theta - combustion_start) / burn_duration
		xb_cur :=
			angle > combustion_start && z_cur < 1 ? 1 - math.exp(-a_wiebe * math.pow(z_cur, m_wiebe + 1)) : (angle <= combustion_start ? 0 : f32(1))
		xb_next :=
			angle > combustion_start && z_next < 1 ? 1 - math.exp(-a_wiebe * math.pow(z_next, m_wiebe + 1)) : (angle <= combustion_start ? 0 : f32(1))
		dxb := xb_next - xb_cur
		dQ := Qin * dxb

		Tg := p * V_cur / (m_air * R_air)
		tdc_pos := piston_position_at_crank_angle(0, crank_offset, rod_length)
		dH_m :=
			(cylinder_height +
				(tdc_pos - piston_position_at_crank_angle(angle, crank_offset, rod_length))) *
			1e-3

		rpm_eff := math.max(rpm, 300)

		mean_ps := 2.0 * stroke * 1e-3 * rpm_eff / 60.0

		h_w :=
			3.26 *
			math.pow(bore * 1e-3, -0.2) *
			math.pow(p * 1e-3, 0.8) *
			math.pow_f32(math.max(Tg, 300), -0.55) *
			math.pow(mean_ps, 0.8)

		A_wall := math.PI * (bore * 1e-3) * math.max(dH_m, 0)
		omega_ref: f32 = 2 * math.PI * rpm_eff / 60.0
		dQ_loss := h_w * A_wall * math.max(Tg - cylinder_temp, 0) * (d_theta / omega_ref)

		dQ_net := dQ - dQ_loss
		dP := ((gamma - 1) / V_cur) * dQ_net - gamma * (p / V_cur) * dV

		if angle < math.to_radians_f32(180) {
			p = manifold_pressure * 1e3
		} else if angle > math.to_radians_f32(540) {
			p = manifold_pressure * 1e3
		} else {
			p += dP
		}

		p = math.max(p, manifold_pressure * 1e3 * 0.3)

		state.p_trace[i] = p / 1e3
		state.w_net += p * dV
	}

	return state
}

draw_assembly :: proc(
	crank_angle: f32,
	piston_y: f32,
	vis_intake_valve_pos: f32,
	vis_exhaust_valve_pos: f32,
	piston_head: rl.Texture,
	rod: rl.Texture,
	crankshaft: rl.Texture,
	valve: rl.Texture,
	engine_block: rl.Texture,
	sparkplug: rl.Texture,
	x: f32 = 0,
	y: f32 = 0,
	scale: f32 = 1,
) {
	valve_ar := f32(valve.height) / f32(valve.width)

	iv_x := 35 + vis_intake_valve_pos * math.sin(math.to_radians_f32(15))
	iv_y := 14 + vis_intake_valve_pos * math.cos(math.to_radians_f32(-15))

	iv_height := (14.5 * valve_ar * scale)

	rl.DrawTexturePro(
		valve,
		{0, 0, f32(valve.width), f32(valve.height)},
		{x + iv_x * scale, y + iv_height + iv_y * scale, 14.5 * scale, 14.5 * valve_ar * scale},
		{0, iv_height},
		-15,
		rl.WHITE,
	)

	ev_x := 67.5 + vis_exhaust_valve_pos * math.sin(math.to_radians_f32(-15))
	ev_y := 14 + vis_exhaust_valve_pos * math.cos(math.to_radians_f32(-15))

	ev_height := (14.5 * valve_ar * scale)

	rl.DrawTexturePro(
		valve,
		{0, 0, f32(valve.width), f32(valve.height)},
		{
			x + (f32(ev_x) + 14.5) * scale,
			y + ev_height + ev_y * scale,
			14.5 * scale,
			14.5 * valve_ar * scale,
		},
		{14.5 * scale, ev_height},
		15,
		rl.WHITE,
	)

	piston_head_ar := f32(piston_head.height) / f32(piston_head.width)

	rl.DrawTexturePro(
		piston_head,
		{0, 0, f32(piston_head.width), f32(piston_head.height)},
		{x + 32 * scale, y + (53 + piston_y) * scale, 52.2 * scale, 52.2 * piston_head_ar * scale},
		{0, 0},
		0,
		rl.WHITE,
	)

	crankshaft_ar := f32(crankshaft.height) / f32(crankshaft.width)
	crank_w := 54.8 * scale
	crank_h := 54.8 * crankshaft_ar * scale

	rl.DrawTexturePro(
		crankshaft,
		{0, 0, f32(crankshaft.width), f32(crankshaft.height)},
		{x + 58 * scale, y + 169 * scale, crank_w, crank_h},
		{crank_w / 2, crank_h / 2},
		math.to_degrees(-crank_angle),
		rl.WHITE,
	)

	rod_ar := f32(rod.height) / f32(rod.width)

	rod_start_x: f32 = 58
	rod_start_y: f32 = 70 + piston_y

	crank_center_x: f32 = 58
	crank_center_y: f32 = 169
	rod_end_x := crank_center_x - 20 * math.sin(crank_angle)
	rod_end_y := crank_center_y - 20 * math.cos(crank_angle)

	rdx := rod_end_x - rod_start_x
	rdy := rod_end_y - rod_start_y
	rod_angle := math.to_degrees_f32(math.atan2_f32(rdx, rdy))

	rl.DrawTexturePro(
		rod,
		{0, 0, f32(rod.width), f32(rod.height)},
		{x + rod_start_x * scale, y + rod_start_y * scale, 34 * scale, 34 * rod_ar * scale},
		{34 * scale / 2, 0},
		-rod_angle,
		rl.WHITE,
	)

	engine_block_ar := f32(engine_block.height) / f32(engine_block.width)

	rl.DrawTexturePro(
		engine_block,
		{0, 0, f32(engine_block.width), f32(engine_block.height)},
		{x + 0 * scale, y + 40 * scale, 117 * scale, 117 * engine_block_ar * scale},
		{0, 0},
		0,
		rl.WHITE,
	)

	sparkplug_ar := f32(sparkplug.height) / f32(sparkplug.width)

	rl.DrawTexturePro(
		sparkplug,
		{0, 0, f32(sparkplug.width), f32(sparkplug.height)},
		{x + 52 * scale, y - 3 * scale, 14 * scale, 14 * sparkplug_ar * scale},
		{0, 0},
		0,
		rl.WHITE,
	)
}

synth_sample :: proc() {

}

main :: proc() {
	rl.SetConfigFlags({.WINDOW_RESIZABLE, .MSAA_4X_HINT})
	rl.InitWindow(1280, 720, "Engine Sim")

	bore: f32 = 85
	rod_length: f32 = 140
	crank_offset: f32 = 45
	cylinder_height: f32 = 10
	intake_valve_diameter: f32 = 30
	valve_lift: f32 = 10
	rpm: f32 = 0
	manifold_pressure: f32 = 101.325
	ratio_of_specific_heats: f32 = 1.35
	cylinder_temp: f32 = 400

	exhaust_valve_diameter: f32 = 0
	exhaust_valve_pos: f32 = 0
	intake_valve_pos: f32 = 0

	vis_rod_length: f32 = 70
	vis_crank_offset: f32 = 21
	vis_valve_lift: f32 = 10

	crank_angle: f32 = 0
	power: f32 = 0
	torque: f32 = 0

	BUF :: 1024
	samples: [BUF]f32

	throttle: f32 = 0
	flywheel_inertia: f32 = 0.05
	load_torque: f32 = 5
	breakaway_fric_c0: f32 = 1.5
	vicious_fric_c1: f32 = 0.1

	cycle := compute_cycle(
		bore,
		crank_offset,
		rod_length,
		cylinder_height,
		ratio_of_specific_heats,
		manifold_pressure,
		cylinder_temp,
		rpm,
	)

	piston_head := load_texture("piston_head.png")
	rod_tex := load_texture("rod.png")
	crankshaft := load_texture("crankshaft.png")
	valve := load_texture("valve.png")
	engine_block := load_texture("engine_block.png")
	sparkplug := load_texture("sparkplug.png")

	phase: f32 = 0

	/*
	submit_score("hi", 400)
	entries := get_leaderboard()
	fmt.print(entries)
	*/

	rl.InitAudioDevice()

	rl.SetAudioStreamBufferSizeDefault(BUF)
	stream: rl.AudioStream = rl.LoadAudioStream(44100, 32, 1)

	rl.PlayAudioStream(stream)

	for !rl.WindowShouldClose() {
		if rl.IsKeyDown(.UP) do throttle += 1.0 * rl.GetFrameTime()
		else do throttle -= 1.0 * rl.GetFrameTime()

		throttle = clamp(throttle, 0, 1)

		manifold_pressure = 20 + (101.325 - 20) * throttle

		cycle = compute_cycle(
			bore,
			crank_offset,
			rod_length,
			cylinder_height,
			ratio_of_specific_heats,
			manifold_pressure,
			cylinder_temp,
			rpm,
		)

		tau_gas := cycle.w_net / (4 * math.PI)

		omega := rpm * 2 * math.PI / 60
		tau_friction := breakaway_fric_c0 + vicious_fric_c1 * omega
		tau_net := tau_gas - tau_friction - load_torque

		alpha := tau_net / flywheel_inertia

		omega += alpha * rl.GetFrameTime()
		omega = math.max(omega, 0)
		rpm = omega * 60 / (2 * math.PI)
		rpm = clamp(rpm, 0, 30000)

		crank_angle += omega * rl.GetFrameTime()

		power = cycle.w_net * (rpm / 60) / 2
		torque = power / math.max(omega, 0.01)

		crank_angle = math.mod(crank_angle, 4 * math.PI)

		angle_idx := int(crank_angle / (4 * math.PI) * ANGLE_STEPS) % ANGLE_STEPS
		p_cycle := cycle.p_trace[angle_idx]

		if rl.IsAudioStreamProcessed(stream) {
			for i in 0 ..< BUF {
				freq := rpm / 120.0
				phase += freq / f32(44100)
				if phase >= 1.0 {phase -= 1.0}
				samples[i] = math.sin(phase * 2.0 * math.PI) * 5
			}
			rl.UpdateAudioStream(stream, raw_data(samples[:]), BUF)
		}

		rl.BeginDrawing()
		rl.ClearBackground({240, 240, 240, 255})

		vis_tdc_pos := piston_position_at_crank_angle(0, vis_crank_offset, vis_rod_length)
		piston_y :=
			vis_tdc_pos -
			piston_position_at_crank_angle(crank_angle, vis_crank_offset, vis_rod_length)

		vis_intake_valve_pos := valve_position_at_angle(
			crank_angle,
			math.to_radians_f32(168),
			math.to_radians_f32(12),
			vis_valve_lift,
		)
		vis_exhaust_valve_pos := valve_position_at_angle(
			crank_angle,
			math.to_radians_f32(212),
			math.to_radians_f32(450 + 48),
			vis_valve_lift,
		)

		exhaust_valve_pos = valve_position_at_angle(
			crank_angle,
			math.to_radians_f32(212),
			math.to_radians_f32(450 + 48),
			10,
		)
		intake_valve_pos = valve_position_at_angle(
			crank_angle,
			math.to_radians_f32(168),
			math.to_radians_f32(12),
			10,
		)
		exhaust_valve_diameter = intake_valve_diameter * 0.75

		for x: i32 = 0; x < rl.GetRenderWidth(); x += 30 {
			rl.DrawLine(x, 0, x, rl.GetRenderHeight(), {0, 0, 255, 40})
		}
		for y: i32 = 0; y < rl.GetRenderHeight(); y += 30 {
			rl.DrawLine(0, y, rl.GetRenderWidth(), y, {0, 0, 255, 40})
		}

		rl.DrawText(rl.TextFormat("%.1f HP", power / 745.7), 100, 260, 10, rl.BLACK)
		rl.DrawText(rl.TextFormat("%.1f Nm", torque), 100, 280, 10, rl.BLACK)
		rl.DrawText(rl.TextFormat("%.1f kPa", p_cycle), 100, 300, 10, rl.BLACK)
		rl.DrawText(
			rl.TextFormat("%.1f deg", math.to_degrees(crank_angle)),
			100,
			320,
			10,
			rl.BLACK,
		)
		rl.DrawText(rl.TextFormat("%.1f kPa MAP", manifold_pressure), 100, 230, 10, rl.BLACK)
		rl.DrawText(rl.TextFormat("%.1f RPM", rpm), 100, 250, 10, rl.BLACK)
		/*
		rl.GuiSlider({100, 50, 100, 20}, "Bore", rl.TextFormat("%.1f mm", bore), &bore, 50, 150)
		rl.GuiSlider(
			{100, 70, 100, 20},
			"Rod Length",
			rl.TextFormat("%.1f mm", rod_length),
			&rod_length,
			100,
			200,
		)
		rl.GuiSlider(
			{100, 90, 100, 20},
			"Crank Offset",
			rl.TextFormat("%.1f mm", crank_offset),
			&crank_offset,
			25,
			70,
		)
		rl.GuiSlider(
			{100, 110, 100, 20},
			"Cyl Ceiling",
			rl.TextFormat("%.1f mm", cylinder_height),
			&cylinder_height,
			8,
			15,
		)
		rl.GuiSlider(
			{100, 130, 100, 20},
			"Flywheel Inertia",
			rl.TextFormat("%.1f mm", flywheel_inertia),
			&flywheel_inertia,
			0,
			2,
		)
		rl.GuiSlider(
			{100, 170, 100, 20},
			"Wall Temp",
			rl.TextFormat("%.0f K", cylinder_temp),
			&cylinder_temp,
			300,
			600,
		)
*/

		rl.GuiSlider(
			{100, 150, 100, 20},
			"Throttle",
			rl.TextFormat("%.0f %%", throttle * 100),
			&throttle,
			0,
			1,
		)

		draw_assembly(
			crank_angle,
			piston_y,
			vis_intake_valve_pos,
			vis_exhaust_valve_pos,
			piston_head,
			rod_tex,
			crankshaft,
			valve,
			engine_block,
			sparkplug,
			f32(rl.GetRenderWidth() / 3),
			50,
			4,
		)

		rl.EndDrawing()
	}

	rl.UnloadAudioStream(stream)
	rl.CloseAudioDevice()

	rl.CloseWindow()
}
