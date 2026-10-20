/-
**The whole program, through the open bridge.**

`pilot2_promising_of_envGValsBridge`: `pilot_promising` (`Lower/PilotWhole.lean`)
for `pilot2`, conditional on two named obligations, `EnvGValsBridge (treiber2GA
t n0 n1)` (`Lower/Pilot2Bridge.lean`) and `Pilot2ValsReach`; every other premise
of the bridge is discharged (static facts, `hB_P2`, the `QA64CAdjV` starts from
`main_partialTripleEnv2`, the purity specifications from `main_pure2`, the
final-configuration argument). One layout `l` for both threads (narrower than
`pilot_promising`'s `l0`/`l1`). `pilot2_promising_concrete`: the explorer's
configuration (`pilot2Run`), stacks included.
-/
import Kraken.Promising.Lower.Pilot2Pure
import Kraken.Promising.Lower.PilotWhole

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.DStack

namespace Kraken.Promising.Lower.Pilot2

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.SLR.EnvG.Treiber (initVal_eq)

/-- **The second open obligation**: every configuration reachable from the
start keeps the Treiber value invariant (`top` and both links hold `0`, `n0` or
`n1`). It follows from value specifications of `pilot2` in
`SharedEnv.inv (treiber2SA t n0 n1) (treiber2GA t n0 n1)` by
`InvLinkAArch64.inv_reachable` (the `DStackTreiber2A64` proof style, with
`HeapOff` for the frame); not done here. A per-thread value specification would
replace both this and `EnvGValsBridge`. -/
def Pilot2ValsReach (t n0 n1 : BitVec 64) (s0 s1 : isa.State) (initMem : List (Loc × Val)) : Prop :=
  ∀ fuel c, Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) c → MemInv (treiber2GA t n0 n1) c.mem

section Whole

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot2)]

/-- `pilot2`'s postcondition: the end of its text and `DnD`. -/
abbrev postP2 (P : Params) (w : Nat) : MachineState × EStateA → Prop :=
  postOf pilot2 fun s σ => ∃ _ : Nat, DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ

omit [Executable.ValidLayout (layout pilot2)] in
/-- **`hB` for thread `w`** (`Pilot.hB_P` for `pilot2`). -/
theorem hB_P2 (P : Params) {w : Nat} (hw : w < 2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postP2 P w (t.st.st, σ) → t.prom = [] → EnvRel w (plan P w) σ c t r g cl → cl → TB2D P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact ⟨w, hw, t, hrel.ht, hcom.2.2.1, by rw [initVal_eq hrel.snap.init]; exact hcom.2.2.2.1,
      hd.imp (DonePopD.mono hpre) (DoneCbz.mono hpre)⟩
  · rw [hp] at hts; cases hts

omit [Executable.ValidLayout (layout pilot2)] in
/-- **A thread's start state for `pilot2`**: `Pilot.StartP` with the
private-stack interface (the heap off `dmem`, `[lo, lo + nb)` mapped) in place of "no
private word", `sp` 16-byte aligned and the frame slot inside the region. -/
structure StartP2 (P : Params) (w : Nat) (d : BitVec 32) (lo : BitVec 64) (nb : Nat) (s : isa.State) : Prop where
  exe : s.exe = layout pilot2
  decls : s.decls = {}
  endPc : s.endPc = (layout pilot2).addrOf pilot2.length
  pc : s.st.2 = (layout pilot2).addrOf 0
  x30 : Int64.ofBitVec s.st.1.regs.X30.toBitVec = (layout pilot2).addrOf pilot2.length
  x21 : s.st.1.regs.X21.toBitVec = P.t
  x27 : s.st.1.regs.X27.toBitVec = P.n w
  x28 : s.st.1.regs.X27.toBitVec + 16 ≤ s.st.1.regs.X28.toBitVec
  x9 : s.st.1.regs.X9.toBitVec.setWidth 32 = d
  stack : StackOK P lo nb s.st.1.dmem
  sp : s.st.1.regs.SP.toBitVec % 16#64 = 0
  slot : (s.st.1.regs.SP.toBitVec - 16#64 - lo).toNat + 8 ≤ nb

/-- **Thread `w`'s start judgment** in `EnvGCAdjV` (the bridge's per-thread
premise), from `main_partialTripleEnv2`. -/
theorem start_P2 {P : Params} (hL : TLocs P) {w : Nat} (hw : w < 2) {d9 : BitVec 32}
    (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) {lo : BitVec 64} {nb : Nat} {s : isa.State}
    (hS : StartP2 P w d9 lo nb s) {c : Config isa} (hT0 : c.mem.initVal P.top = 0) :
    QA64CAdjV Arch.armv8 w (plan P w) (GV P) (layout pilot2) ((layout pilot2).addrOf pilot2.length) (postP2 P w) s
      (σInit c (thrRes c.mem P w) (ghost₀ P)) := by
  letI : CodeEnv := ⟨layout pilot2⟩
  exact ⟨hS.exe, hS.decls, hS.endPc, safely_start_of_partialTripleEnv
    (main_partialTripleEnv2 P w hL hw d9 lo nb hD).uncount rfl hS.pc
    ⟨0, hS.x30, hS.x21, hS.x27, hS.x28, hS.x9, hS.stack, hS.sp, hS.slot, pu0_init P hL hw _ hT0⟩ (by simp)⟩

/-- The purity specification of `pilot2`. -/
def pilot2PureSpec (rel : Loc → Pred) : RelPureSpec Arch.armv8 rel :=
  RelPureSpec.ofProgram pilot2 fun _ _ => ∃ _ : Nat, True

theorem pilot2PureSpec_holds {rel : Loc → Pred} {P : Params} {w : Nat} (hw : w < 2) {d9 : BitVec 32}
    {lo : BitVec 64} {nb : Nat} (hd : ∀ v : Val, Pred.Pure (rel ⟨P.n w, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨P.n w + 8, 8⟩) v) {s : isa.State} (hS : StartP2 P w d9 lo nb s) :
    (pilot2PureSpec rel).Holds s := by
  letI : CodeEnv := ⟨layout pilot2⟩
  exact RelPureSpec.holds_of_partialTripleEnv (main_pure2 rel P w hw lo nb hd hn).uncount rfl hS.exe hS.decls
    hS.endPc hS.pc ⟨0, hS.x30, hS.x21, hS.x27, hS.x28, hS.stack, hS.sp, hS.slot⟩

/-- **The hand-lowered two-thread Treiber client with a `dmem` frame, on the
Promising model, given the two open obligations** (AArch64, `Arch.armv8`):
`pilot_promising`'s conclusion for `pilot2`, from `StartP2` starts (stacks
`[lo0, lo0 + nb0)`, `[lo1, lo1 + nb1)` off the heap), the bridge
`EnvGValsBridge (treiber2GA t n0 n1)` and `Pilot2ValsReach`. -/
theorem pilot2_promising_of_envGValsBridge {t n0 n1 : BitVec 64} (hBr : EnvGValsBridge (treiber2GA t n0 n1)) {fuel : Nat}
    (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} {lo0 lo1 : BitVec 64} {nb0 nb1 : Nat}
    (h0 : StartP2 (tPD t n0 n1) 0 1 lo0 nb0 s0) (h1 : StartP2 (tPD t n0 n1) 1 2 lo1 nb1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hvals : Pilot2ValsReach t n0 n1 s0 s1 initMem)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg := by
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  have hrel : ∀ (l : Loc), l ≠ (tPD t n0 n1).top → ∀ v, Pred.Pure ((ghost₀ (tPD t n0 n1)).rel l) v :=
    fun l hl v => by rw [ghost₀_rel_ne hl]; exact Pred.emp_pure v
  refine hBr Arch.armv8 fuel [s0, s1] initMem _ (ghost₀ (tPD t n0 n1)) (TB2D (tPD t n0 n1))
    (Treiber2DFinal n0 n1) (plan (tPD t n0 n1)) (fun _ => layout pilot2)
    (fun _ => (layout pilot2).addrOf pilot2.length) (fun w => postP2 (tPD t n0 n1) w)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) rfl (fun _ => pilot2PureSpec _) ?_
    (hvals fuel) ?_ cfg hc hf fun rF' g' E' hle hsize hB => ?_
  · rintro (_ | _ | _) s hs <;> cases hs
    · exact pilot2PureSpec_holds (by decide) (hrel _ (Ne.symm (top_dd _ 0))) (hrel _ (hL.top_nd' (by decide)).symm) h0
    · exact pilot2PureSpec_holds (by decide) (hrel _ (Ne.symm (top_dd _ 1))) (hrel _ (hL.top_nd' (by decide)).symm) h1
  · rintro (_ | _ | _) htid
    · exact ⟨inferInstance, plan_valid _ 0, pilot2_rmwLive, pilot2_phase1F, postOf_end,
        not_instrStepEnv_of_end_labels _ 1, hB_P2 _ (by decide), s0, rfl, start_P2 hL (by decide) (fun _ h => h) h0 hT0⟩
    · exact ⟨inferInstance, plan_valid _ 1, pilot2_rmwLive, pilot2_phase1F, postOf_end,
        not_instrStepEnv_of_end_labels _ 1, hB_P2 _ (by decide), s1, rfl, start_P2 hL (by decide) (fun _ h => h) h1 hT0⟩
    · simp at htid; omega
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw (tPD t n0 n1)).mono hle
  have hno := Config.final_not_outstanding hf
  obtain ⟨w0, hw0, th, hth, hd0⟩ := hB 0 (Config.final_done hf hi0)
  obtain ⟨w1, hw1, th', hth', hd1⟩ := hB 1 (Config.final_done hf hi1)
  by_cases hww : w0 = w1
  · subst hww
    exact (acq_pair_false E' hi0 hi1 (by decide) hd0.1 hd1.1).elim
  rcases w0 with _ | _ | w0
  · rcases w1 with _ | _ | w1
    · exact absurd rfl hww
    · refine ⟨th, th', hth, hth', ?_⟩
      rcases final_values_data E' hW hL hno hi0 hi1 hd0 hd1 with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
      · exact .inl ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
      · exact .inr ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
    · omega
  · rcases w1 with _ | _ | w1
    · refine ⟨th', th, hth', hth, ?_⟩
      rcases final_values_data E' hW hL hno hi1 hi0 hd1 hd0 with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
      · exact .inl ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
      · exact .inr ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
    · exact absurd rfl hww
    · omega
  · omega

end Whole

/-! ## The concrete instance (`Pilot2Prog`'s explorer configuration) -/

/-- The domain of `stackMem lo k`: the bytes `[lo, lo + 8k)`. -/
theorem stackMem_isSome (lo : BitVec 64) : ∀ k, k ≤ 8 → ∀ a,
    ((stackMem lo k).get? a).isSome = decide ((a - lo).toNat < 8 * k)
  | 0, _, a => by simp [stackMem]
  | k + 1, hk, a => by
    rw [stackMem, Mem.storeInt, Mem.get?_storeBytes, Option.isSome_or, stackMem_isSome lo k (by omega) a]
    rw [Std.ExtHashMap.get?_eq_getElem?, get?_At _ _ _ (by simp [Int.toBytes_length])]
    have hl : ∀ (l : List UInt8) i, l[i]?.isSome = decide (i < l.length) := fun l i => by
      by_cases h : i < l.length <;> simp [h]
    simp only [hl, Int.toBytes_length, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    have hlo := lo.isLt; have ha := a.isLt
    rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega

/-- A start stack `[lo, lo + 64)` away from the heap satisfies the stack
interface. -/
theorem stackOK_stackMem {P : Params} {lo : BitVec 64} (h : ∀ k, HP P k → 64 ≤ (k - lo).toNat) :
    StackOK P lo 64 (stackMem lo 8) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have h1 := stackMem_isSome lo 8 (Nat.le_refl 8) k
    rw [decide_eq_false (by have := h k hk; omega)] at h1
    cases hg : (stackMem lo 8).get? k
    · rfl
    · rw [hg] at h1; cases h1
  · rw [stackMem_isSome lo 8 (Nat.le_refl 8)]; simpa [InRange] using hk

section
attribute [local instance] pLayout2

theorem thread2_start (base v sp : UInt64) {w : Nat} (d : BitVec 32)
    (hn : base.toBitVec = (tPD 0x1000 0x2000 0x3000).n w) (hlim : base.toBitVec + 16 ≤ (base + 0x100).toBitVec)
    (hd : v.toBitVec.setWidth 32 = d) (hsp : sp.toBitVec % 16#64 = 0)
    (hh : ∀ k, HP (tPD 0x1000 0x2000 0x3000) k → 64 ≤ (k - (sp.toBitVec - 64)).toNat) :
    StartP2 (tPD 0x1000 0x2000 0x3000) w d (sp.toBitVec - 64) 64 (thread2 base v sp) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, hn, hlim, hd, stackOK_stackMem hh, hsp, ?_⟩ <;> try (simp only [thread2]; decide)
  simp only [thread2]
  rw [show sp.toBitVec - 16#64 - (sp.toBitVec - 64) = 48#64 by bv_omega]
  decide

theorem heap_far {lo : BitVec 64} (hlo : lo = 0x8000#64 ∨ lo = 0x9000#64) :
    ∀ k, HP (tPD 0x1000 0x2000 0x3000) k → 64 ≤ (k - lo).toNat := by
  rintro k ⟨b, m, hm, hb⟩
  simp [SLay, treiber2SA, tPD] at hm
  rcases hlo with rfl | rfl <;>
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> bv_omega

/-- **Non-vacuity**: `pilot2_promising_of_envGValsBridge` at the explorer's
configuration (`pilot2Run`, `Lower/Pilot2Prog.lean`): `top` at `0x1000`, arenas
at `0x2000`/`0x3000`, payloads `1`/`2`, stacks `[0x8000, 0x8040)` and
`[0x9000, 0x9040)`; conditional on the two open obligations at this instance. -/
theorem pilot2_promising_concrete (hBr : EnvGValsBridge (treiber2GA 0x1000 0x2000 0x3000))
    (hvals : Pilot2ValsReach 0x1000 0x2000 0x3000 (thread2 0x2000 1 0x8040) (thread2 0x3000 2 0x9040)
      Pilot.initMem) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [thread2 0x2000 1 0x8040, thread2 0x3000 2 0x9040] Pilot.initMem) c)
    (hf : c.final = true) : Treiber2DFinal 0x2000 0x3000 c :=
  pilot2_promising_of_envGValsBridge hBr (by decide) (by decide) (by decide) (by decide) (by decide)
    (thread2_start _ _ _ _ rfl (by decide) (by decide) (by decide) (heap_far (.inl (by decide))))
    (thread2_start _ _ _ _ rfl (by decide) (by decide) (by decide) (heap_far (.inr (by decide))))
    (by simp only [Config.init_mem]; decide) hvals hc hf

end

end Kraken.Promising.Lower.Pilot2
