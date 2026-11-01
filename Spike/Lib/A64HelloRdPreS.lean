/-
**hello.w's `wc_rodata` up to the allocator's return placed at the setup call's frame** (AArch64;
`RdWfSF.rdPreW_WSHF`'s `hpl` at `fs = [HelloRdCf.frH env]`, region `Hello1.mR R`, frame condition
`Hello1.mF R F m0 σC`): the prologue's, the entry block's and the allocator's states are placed (`PlacedSE` at the
frame) once every control of `wc_rodata`'s entry invariant `J0` and of the allocator's caller `J1` is placed at
every state (`hc`; at `rodata`'s allocation `rdCN` by `placed_rdCN`).

The frame's only free variable `me` is a slot of `scc_rt_main`'s frame at or above its `sp` (`RdPlS.FrP`), kept
by the callee (`CKept`, from `mF`) and outside the callee's region (`DFrame`): the prologue and the entry block
run in `mR R`, the allocator in `aR (mR R)` (`dframe_mR`).

- `placed_rdCN`: `rodata`'s control at its allocation is placed at every state, given `m`'s immediate at `eB`.
- `placedSE_fr`: a placed control placed at the frame.
- `dframe_mR`: memory kept off the allocator's region is kept off `wc_rodata`'s.
- `blkW_fr`, `nodeW_fr`, `allocW_fr`: the nodes placed.
- `rdPreW_frS`, `rdPreW_frS_rdCN`: `RdPreW` inside the placement at `[frH env]`.
-/
import Spike.Lib.A64HelloRdPlS

namespace Spike.Lib.A64.HelloPh.RdPreS

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib (Ctl Region)
open Spike.Lib.A64Consumer (Lbl Placed)
open Spike.Lib.A64ConsumerS (PlacedSE PlacedS)
open Spike.Lib.A64.Flow (ND BlkW NodeW)
open Spike.Lib.A64.Flow.HelloRd (rN RdPreW RdCtx)
open Spike.Lib.A64.Flow.Hello1 (mR mF aR)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW)
open Spike.Lib.HelloRodataSrc (eB rdCN)
open Spike.Lib.HelloRdCf (frH)
open Spike.Lib.A64.HelloPh.RdPlS (FrP placed_of_tbl framesPlaced_frH)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State}

/-! ## `rodata`'s control at its allocation -/

/-- **`rodata`'s control at its allocation is placed** at every state: its only free variable `m` is the
immediate `2` (`h`). -/
theorem placed_rdCN (h : Λ.imms eB "m" 0 = some 2) : Placed Λ lbl s rdCN := by
  have hfv : ∀ x ∈ exprFv rdCN.term, x = "m" := by
    intro x hx
    simp only [show exprFv rdCN.term = ["m", "m"] by decide, List.mem_cons, List.not_mem_nil, or_false,
      or_self] at hx
    exact hx
  refine placed_of_tbl [("m", [.imm 2])] ?_ ?_ ?_
  · intro x hx ty ws hl
    obtain rfl := hfv x hx
    simp [rdCN, lookupE, Spike.Lib.Hello1RodataSrc.envN] at hl
    exact ⟨_, rfl, by simp [← hl.2]⟩
  · intro x pls ty ws hpls hl k wp wd hwp hwd
    by_cases e : x = "m"
    · subst e; cases hpls
      simp [rdCN, lookupE, Spike.Lib.Hello1RodataSrc.envN] at hl
      rw [← hl.2] at hwd
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact ⟨by decide, rfl⟩
      | _ + 1, hwp, _ => simp at hwp
    · simp [List.lookup, beq_false_of_ne e] at hpls
  · intro x hx pls k n hpls hn
    obtain rfl := hfv x hx
    cases hpls
    match k, hn with
    | 0, hn => cases hn; exact h
    | _ + 1, hn => simp at hn

/-! ## The setup call's frame -/

section Nodes

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {m0 : MachineData}
  {σC : Spike.Lib.A64.Flow.AS} {env : Env}

/-- **A placed control is placed at the setup call's frame** below `wc_rodata`'s call. -/
theorem placedSE_fr (hP : FrP lbl R env σC) {c : Ctl} (hc : Placed Λ lbl s c) {m1 m' : MachineData}
    (hK : Spike.Lib.A64.Flow.CKept R (-80) (-208) 0 m1 m') (hA : Spike.Lib.A64.Flow.Abs R ⟨-80, []⟩ m1 σC)
    (hD : Spike.Lib.A64.Flow.DFrame (mR R) m' s.st.1) : PlacedSE Λ lbl s c [frH env] :=
  let ⟨_, _, hkm, hme, hlm⟩ := hP.km
  .inl (PlacedS.ofFrames hc (framesPlaced_frH hP.ok hP.lo hP.hi hkm hme hlm hK hA hD))

/-- **Memory kept off the allocator's region is kept off `wc_rodata`'s** (`aR (mR R)` inside `mR R`). -/
theorem dframe_mR (hR : R.OK) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi) {m m' : MachineData}
    (h : Spike.Lib.A64.Flow.DFrame (aR (mR R)) m m') : Spike.Lib.A64.Flow.DFrame (mR R) m m' := by
  have hmR : (mR R).OK := Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  have hb := Region.callee_base (hi' := 0) hmR (kc := -48) (lo' := -160)
    (by simp only [mR, Region.callee]; omega) (by decide) (by simp only [mR, Region.callee]; omega)
  intro x hx hout
  refine h x hx ?_
  simp only [aR, mR, Region.callee] at hb hout ⊢
  omega

set_option hygiene false in
/-- The placement at the labels `lbl`, the setup call's frame. -/
local notation "PL" => fun s c => PlacedSE Λ lbl s c [frH env]

/-- **A block is placed** once its invariant's controls are placed at every state (`hc`). -/
theorem blkW_fr (hP : FrP lbl R env σC) {n : ND} {blk : List Directive}
    (hc : ∀ σ c, n.J σ c → ∀ s, Placed Λ lbl s c) :
    BlkW (PL) (fun _ _ => False) exe endPc (mR R) (mF R F m0 σC) n blk := by
  intro s σ c _ _ _ _ _ hF hJ k _ m _ hD
  exact ⟨placedSE_fr hP (hc σ c hJ _) hF.2.1 hF.2.2 hD, fun _ h => h⟩

/-- **A node is placed** once its invariant's controls are placed at every state (`hc`). -/
theorem nodeW_fr (hP : FrP lbl R env σC) {n : ND} (hc : ∀ σ c, n.J σ c → ∀ s, Placed Λ lbl s c) :
    NodeW (PL) (fun _ _ => False) exe endPc (mR R) (mF R F m0 σC) n := by
  rintro s c ⟨-, -, -, -, σ, -, hF, hJ⟩
  exact ⟨placedSE_fr hP (hc σ c hJ _) hF.2.1 hF.2.2 (Spike.Lib.A64.Flow.DFrame.refl _ _), fun _ h => h⟩

/-- **`scc_rt_alloc` is placed** at `wc_rodata`'s call: its controls are the call's (or its hold), the
allocator's caller's (`J1`), placed at every state (`hc`). -/
theorem allocW_fr (hP : FrP lbl R env σC) (hlo : R.lo ≤ -288) {ms : Spike.Lib.MemSide isaLSE2}
    {J0 J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop} (hc : ∀ σ c, J1 σ c → ∀ s, Placed Λ lbl s c) (q : Call) :
    AllocW ms q (PL) (fun _ _ => False) exe endPc (aR (mR R))
      (fun m => mF R F m0 σC m ∧ CallerCells (mR R) (-48) (-160) 0 m ∧
        RdCtx ms (_root_.Executable.labels exe).label (mR R) J0 J1 q m) :=
  Spike.Lib.A64SetupPlaced.allocW_of_ctl fun _ hF s c hD hcq => by
    obtain ⟨⟨-, hK, hA⟩, -, _, _, c', -, ⟨⟨σe, hJe, -⟩, -⟩, hN, -⟩ := hF
    have hq := Spike.Lib.A64SetupPlaced.ctl_of_N _ ms q .e _ c' hN
    have h0 := hc σe c' hJe s
    have hpl : Placed Λ lbl s c := by
      rcases hq with rfl | ⟨_, rfl⟩ <;> rcases hcq with rfl | ⟨_, rfl⟩ <;> exact h0
    exact placedSE_fr hP hpl hK hA (dframe_mR hP.ok hlo hP.hi hD)

end Nodes

/-! ## `wc_rodata` up to the allocator's return -/

/-- **`wc_rodata` up to the allocator's return inside the placement at the setup call's frame**
(`RdWfSF.rdPreW_WSHF`'s `hpl` at `[frH env]`, region `Hello1.mR R`, frame condition `Hello1.mF R F m0 σC`): every
control of the entry invariant `J0` and of the allocator's caller `J1` is placed at every state (`hc`), the
frame's `me` is a caller's slot (`hP`), the caller's region reaches the allocator's (`hlo`). -/
theorem rdPreW_frS {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {m0 : MachineData} {σC : Spike.Lib.A64.Flow.AS} {env : Env} {ms : Spike.Lib.MemSide isaLSE2}
    {J0 J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop} (hP : FrP lbl R env σC) (hlo : R.lo ≤ -288)
    (hc : ∀ σ c, J0 σ c ∨ J1 σ c → ∀ s, Placed Λ lbl s c) :
    RdPreW (fun s c => PlacedSE Λ lbl s c [frH env]) (fun _ _ => False) exe endPc (mR R) (mF R F m0 σC) ms
      J0 J1 :=
  ⟨⟨blkW_fr hP fun σ c h => hc σ c (.inl h),
      nodeW_fr hP fun _ c ⟨σ, h, _⟩ => hc σ c (.inl h),
      blkW_fr hP fun _ c ⟨σ, _, h, _⟩ => hc σ c (.inl h),
      blkW_fr hP fun _ c ⟨σ, _, h, _⟩ => hc σ c (.inl h)⟩,
    blkW_fr hP fun _ c ⟨σe, h, _⟩ => hc σe c (.inl h),
    fun q _ _ => allocW_fr hP hlo (fun σ c h => hc σ c (.inr h)) q⟩

/-- **`rdPreW_frS` at `rodata`'s allocation**: every control of `J0` and `J1` is `rdCN` (`hc`), `m`'s immediate
at `eB` is `2` (`hm`). -/
theorem rdPreW_frS_rdCN {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {m0 : MachineData} {σC : Spike.Lib.A64.Flow.AS} {env : Env} {ms : Spike.Lib.MemSide isaLSE2}
    {J0 J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop} (hP : FrP lbl R env σC) (hlo : R.lo ≤ -288)
    (hm : Λ.imms eB "m" 0 = some 2) (hc : ∀ σ c, J0 σ c ∨ J1 σ c → c = rdCN) :
    RdPreW (fun s c => PlacedSE Λ lbl s c [frH env]) (fun _ _ => False) exe endPc (mR R) (mF R F m0 σC) ms
      J0 J1 :=
  rdPreW_frS hP hlo fun σ c h _ => hc σ c h ▸ placed_rdCN hm

end Spike.Lib.A64.HelloPh.RdPreS

/-- info: 'Spike.Lib.A64.HelloPh.RdPreS.placed_rdCN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdPreS.placed_rdCN

/-- info: 'Spike.Lib.A64.HelloPh.RdPreS.rdPreW_frS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdPreS.rdPreW_frS

/--
info: 'Spike.Lib.A64.HelloPh.RdPreS.rdPreW_frS_rdCN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdPreS.rdPreW_frS_rdCN
