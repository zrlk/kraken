/-
**`wc_waitLoop` inside a state predicate `W`** (AArch64):
`WaitLoop.seg_waitLoop` (`Spike/Lib/A64WaitLoop.lean`) as a `SegLW W`
segment (`Spike/Lib/SegLW.lean`) for any `W`, the obligation that every
state of the loop is in `W` left per node (`LoopW`: `BlkW` for the block
nodes, `NodeW` for the acquire load), the thread-pointer load and the park
call given as `SegW W` segments. wake's main after the spawn instantiates
`W` with `WakeInst.mainW` (off every abort exit, the source off its return,
wide, placed, …).

- `LoopW`: the per-node obligations at one ghost.
- `seg_waitLoopW`: the loop from its entry to its return, inside `W`.
- `seg_parkCallW`: the park call inside `W` (`call_nd_FW` with
  `Park.seg_parkWG`), given the routine's states in `W` in every callee
  frame condition the call can pass (`hPW`: below the caller's, the caller's
  cells outside the callee's region as at the call).
-/
import Spike.Lib.A64WaitLoop
import Spike.Lib.A64CfgLW
import Spike.Lib.A64ParkW

namespace Spike.Lib.A64.WaitLoop

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow
open Scc.Sem (ValRep)

/-- **The loop's states inside `W`**, at one region `R`, frame condition
`F` and the loop's ghosts: every block node's internal states (`BlkW`) and
the acquire load's (`NodeW`). -/
structure LoopW (W : Frag isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (pfx : String) (c0 : Ctl) (x : String) (e : Expr) (ty : Ty)
    (Rd : TermRun.Word → Prop) (A x29 ra tp : BitVec 64) : Prop where
  top : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .e) b0
  n1 : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .n1) (b1 pfx)
  n2 : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .n2) b2
  entry : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .entry) b3
  ld : NodeW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .ld)
  n4 : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .n4) (b4 pfx)
  n5 : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .n5) (b5 pfx)
  then1 : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .then1) b6
  else2 : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .else2) b7
  sp3 : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .sp3) b8

section ProofW

variable {W : Frag isaLSE2} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {pfx : String} {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty}
  {w : TermRun.Word} {A ra tp : BitVec 64} {γ : Sort _} {Rg : γ → Region}
  {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64}

set_option hygiene false in
/-- A block node inside `W`: the block, its `okBlk`, its code and `LoopW`
field; the edge is left. -/
macro "nodeLW " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_fixLW g (SegLW.ofSegW (seg_ndW (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) (hLW g).$f fun σ c hJ => ⟨c, .refl c, ?_⟩)))

/-- **`wc_waitLoop` inside `W`** (`seg_waitLoop` over `SegLW W`): every
block node's and the acquire load's states in `W` (`hLW`), the
thread-pointer load (`htls`) and the park call (`hpark`) segments inside
`W`. -/
theorem seg_waitLoopW (hF : ∀ g, FStable (Rg g) (Fg g)) (hR : ∀ g, (Rg g).OK)
    (hal : ∀ g, (Rg g).base.toNat % 16 = 0) (hlo : ∀ g, (Rg g).lo ≤ -80) (hhi : ∀ g, 0 ≤ (Rg g).hi)
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none)
    (hcode : ∀ g, Code pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label (pfx ++ ".0_entry") =
      (_root_.Executable.labels exe).label "wc_waitLoop" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4)
    (hLW : ∀ g, LoopW W exe endPc (Rg g) (Fg g) pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g)
      ra tp)
    (htls : ∀ g,
      SegW W (fun _ _ => False) p lbl ms
        (At exe endPc (Rg g) (Fg g)
          (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .tls))
        (At exe endPc (Rg g) (Fg g)
          (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .n1)))
    (hpark : ∀ g,
      SegW W (fun _ _ => False) p lbl ms (At exe endPc (Rg g) (Fg g)
          (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .park))
        (fun s c => ∃ g', At exe endPc (Rg g') (Fg g')
          (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g') ra tp .sp3) s c))
    (g0 : γ) :
    SegLW W p lbl ms (At exe endPc (Rg g0) (Fg g0)
        (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g0) ra tp .e))
      (fun s c => ∃ g x', At exe endPc (Rg g) (Fg g)
        (E c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp x') s c) := by
  refine fn_seg_gLW (Rg := Rg) (Fg := Fg)
    (N := fun g => N _ pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp)
    (E := fun g => E c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp) (fun g i => ?_) g0 PN.e
  have hF := hF g; have hR := hR g; have hal := hal g; have hlo := hlo g; have hhi := hhi g
  have hcode := hcode g
  cases i
  case e => nodeLW b0 b0_ok top; rw [N, b0_run]; hit PN.tls
  case tls => exact seg_fixLW g (SegLW.ofSegW (seg_givenW PN.n1 (htls g)))
  case n1 =>
    nodeLW b1 b1_ok n1; rw [N, b1_run, b1T_run, rl_self]
    obtain ⟨hJ, hle⟩ := hJ
    rw [ite_eq_right (by rw [Spike.Lib.A64.Alloc.subs_c]; simpa using hle)]
    hit PN.n2
  case n2 => nodeLW b2 b2_ok n2; rw [N, b2_run]; hit PN.entry
  case entry => nodeLW b3 b3_ok entry; rw [N, b3_run]; hit PN.ld
  case ld =>
    refine seg_fixLW g (ldarSt_ndW (V := 1) hF (fun s he hn => hcode.ld s he hn) (hdm g)
      (fun s c h => ((hLW g).ld s c h).1) ?_)
    rintro m σ c - - ⟨⟨rfl, hJ, htp⟩, h10⟩
    refine ⟨h10, x, a, e, ty, w, hterm, hev, hval, htag, fun v hv => ?_, fun v w' hv hr hr' => ?_⟩
    · refine .inl ⟨PN.n4, rfl, (by decide : SO.le oI (oI.kill .X9) = true), hJ, by rw [ldStep_tp, htp], .inr ⟨?_, rfl⟩⟩
      rw [ldStep_X9]; intro h; exact hv (by rw [h]; rfl)
    · refine .inl ⟨PN.n4, rfl, (by decide : SO.le oI (oI.kill .X9) = true), hJ, by rw [ldStep_tp, htp],
        .inl ⟨?_, w', ⟨hr, hr'⟩, rfl⟩⟩
      rw [ldStep_X9]; exact BitVec.eq_of_toNat_eq (by rw [hv]; rfl)
  case n4 =>
    nodeLW b4 b4_ok n4; rw [N, b4_run, b4T_run, rl_self]
    obtain ⟨hJ, htp, h | h⟩ := hJ
    · rw [ite_eq_left (by rw [Spike.Lib.A64.Alloc.subs_z]; simp [h.1])]
      refine .inl ⟨PN.then1, rfl, rfl, ?_, ?_, h.2, ?_⟩ <;>
        simp_all [JF, Spike.Lib.upd_apply]
    · rw [ite_eq_right (by rw [Spike.Lib.A64.Alloc.subs_z]; simp [h.1])]
      refine .inl ⟨PN.n5, rfl, rfl, h.2, ?_, ?_⟩ <;>
        simp_all [JF, Spike.Lib.upd_apply]
  case n5 => nodeLW b5 b5_ok n5; rw [N, b5_run, b5T_run, rl_self]; hit PN.else2
  case then1 =>
    nodeLW b6 b6_ok then1; rw [N, b6_run]
    refine .inr ⟨PX.ret, ?_, rfl, ?_⟩ <;>
      simp_all [N, E, JF, Past]
  case else2 => nodeLW b7 b7_ok else2; rw [N, b7_run]; hit PN.park
  case park => exact seg_movedLW PN.sp3 (SegLW.ofSegW (hpark g))
  case sp3 => nodeLW b8 b8_ok sp3; rw [N, b8_run]; hit PN.e
  case grow => exact ⟨fun _ _ => False, fun _ _ ⟨_, _, _, _, _, _, _, hJ⟩ => hJ, fun _ _ h => h.elim, fun _ _ h => h.elim⟩
  case ms => exact ⟨fun _ _ => False, fun _ _ ⟨_, _, _, _, _, _, _, hJ⟩ => hJ, fun _ _ h => h.elim, fun _ _ h => h.elim⟩
  case spc => exact ⟨fun _ _ => False, fun _ _ ⟨_, _, _, _, _, _, _, hJ⟩ => hJ, fun _ _ h => h.elim, fun _ _ h => h.elim⟩

/-- **The call of `scc_rt_park` inside `W`** (`seg_parkCall` over `SegW W`:
`call_nd_FW` with `Park.seg_parkWG`). The routine's states are in `W` for
every callee region and frame condition the call passes (`hPW`): the
callee's region below the call's `sp` (offset `-32`; valid and 16-aligned), the condition
stronger than `F`, each of its states' memory outside the callee's
region that of a state at the call, and the routine's ghost source the
caller's (`g.1 = c0`). -/
theorem seg_parkCallW {R : Region} {F : MachineData → Prop} {Rd : TermRun.Word → Prop} {x29 : BitVec 64}
    {c0' : Ctl} {x29' ra' tp' : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi) (hS : Ret0.StOk ms F exe endPc (tp + 16#64) 0#64)
    (htp4 : (tp + 16#64).toNat % 4 = 0) (hpcode : Park.Code c0' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L10_scc_rt_park.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 4 + 4 + 4 + 4)
    (hsp3 : (_root_.Executable.labels exe).label (pfx ++ ".sp3") =
      (_root_.Executable.labels exe).label (pfx ++ ".2_else2") + 4)
    (hPW : ∀ (R' : Region) (F' : MachineData → Prop), R' = R.callee (-32) (-64) 0 → R'.OK →
      R'.base.toNat % 16 = 0 → (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ (mC : MachineData) (σC : Flow.AS) (c : Ctl), Spike.Lib.A64.Flow.Abs R oI mC σC ∧
        (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .park).J σC c ∧
        ∀ k, R.Off k → ¬ R'.Off (k - -32) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      ∀ g : Ctl × BitVec 64 × BitVec 64, g.1 = c0 → Park.ParkGW W exe endPc R' F' g.1 g.2.1 g.2.2 tp) :
    SegW W (fun _ _ => False) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .park))
      (At exe endPc R F (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .sp3)) := by
  refine Ret0.seg_oneW (call_nd_FW (lo' := -64) (hi' := 0) (M := fun _ => True)
    (N := fun _ : Unit => N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .sp3)
    (E := fun e : Empty => e.elim)
    (Ne := fun g : Ctl × BitVec 64 × BitVec 64 => Park.N (_root_.Executable.labels exe).label g.1 g.2.1 g.2.2 tp .e)
    (Ex := fun g y => Park.E g.1 g.2.1 g.2.2 tp y)
    hR hal hF (by show R.lo ≤ -32 + -64; omega) (by decide) (by show (-32 : Int) < R.hi; omega) (by decide)
    (by show (-32 : Int) % 16 = 0; decide) (by decide) (by decide) (KStable.none F) (fun _ _ h => h.elim)
    (fun _ h _ => h)
    (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e _ g hg hm =>
      (Park.seg_parkWG hF' hR' hal' hlo' hhi' hK (hS.mono hFF) htp4 hpcode.ghost hpentry
        (hPW R' F' hR'e hR' hal' hFF (fun m hm' => let ⟨mC, σC, c, hA, hJ, _, hk⟩ := hm m hm'; ⟨mC, σC, c, hA, hJ, hk⟩) g
          (let ⟨_, _, ⟨⟨h1, _⟩, _⟩, h2, _⟩ := hg; h2.symm.trans h1))).mono_post
        fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
    (fun _ => rfl) ?_ ?_)
  · rintro σC c ⟨⟨rfl, -, htp⟩, -⟩
    exact ⟨(c, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec), rfl, rfl, rfl, rfl, htp⟩
  · rintro ⟨c1, x29', ra'⟩ ⟨⟩ σC c σx c' σR ⟨⟨rfl, hJF, -⟩, h30⟩ ⟨hc, -, hra, -⟩ ⟨hc', -, -, htp'⟩ hreg - hslot
    have hout : ∀ k : Int, -32 ≤ k → k % 8 = 0 → k + 8 ≤ 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hslot k ⟨h2, by omega, by omega⟩ fun ⟨_, _, h⟩ => by
        simp only [Region.callee, N] at h; omega
    refine .inl ⟨(), ?_, rfl, hc'.trans hc.symm, ⟨?_, ?_, ?_⟩, ?_⟩
    · subst hra
      show (_root_.Executable.labels exe).label (pfx ++ ".sp3") = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [h30, hsp3, Ret0.ofInt_bmod, BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt]; rfl
    · rw [hout (-16) (by decide) (by decide) (by decide)]; exact hJF.1
    · rw [hout (-8) (by decide) (by decide) (by decide)]; exact hJF.2.1
    · rw [hout (-32) (by decide) (by decide) (by decide)]; exact hJF.2.2
    · show σR.regs.TPIDR_EL0.toBitVec = tp
      rw [hreg]; exact htp'

end ProofW

/-- info: 'Spike.Lib.A64.WaitLoop.seg_waitLoopW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_waitLoopW

/-- info: 'Spike.Lib.A64.WaitLoop.seg_parkCallW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_parkCallW

end Spike.Lib.A64.WaitLoop
