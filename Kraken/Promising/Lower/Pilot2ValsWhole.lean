/-
**The stack-frame pilot without its open obligations.** ISA: AArch64; machine:
the executable Promising machine
(`Reachable Arch.armv8`).

`pilot2_promising`: the conclusion of `pilot2_promising_of_envGValsBridge`
(`Lower/Pilot2Whole.lean`) with **neither** `hBr : EnvGValsBridge (treiber2GA t
n0 n1)` nor `hvals : Pilot2ValsReach t n0 n1 s0 s1 initMem`. The proof is
the stack-frame pilot's with `hBr` replaced by the value bridge's `envGValsBridge_ofSpecs`
(`EnvG/ValsA64.lean`), whose value side is
- the per-thread value specification `pilot2ValSpec` (`J tid :=
  (pilot2ValSpec P).Holds`, from `main_val2`, `Lower/Pilot2Vals.lean`; its tree
  law is `threadSpec_allInv`, inside the bridge), at both start states
  (`pilot2ValSpec_holds`, from `StartP2`);
- `MemInv (treiber2GA t n0 n1)` of the initial memory (`memInv_treiber2_init`),
  which asks the two links' initial values to be `0` too (`hN0`, `hN1`, beside
  the stack-frame pilot's `hT0` for `top`).
Every per-thread premise is the stack-frame pilot's (`Vals.QA64CAdjV = Pilot2.QA64CAdjV` by
`rfl`). Phase-1 limits apply (`Phase1TreeF`).
-/
import Kraken.Promising.Lower.Pilot2Vals
import Kraken.Promising.Lower.Pilot2Whole

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.DStack

namespace Kraken.Promising.Lower.Pilot2

open Kraken.Promising.SLR.EnvG.Treiber2

/-- The initial memory satisfies the Treiber value invariant when `top` and
both links start at `0`. -/
theorem memInv_treiber2_init {t n0 n1 : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hT0 : (Config.init states initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init states initMem).mem.initVal ⟨n0 + 8, 8⟩ = 0)
    (hN1 : (Config.init states initMem).mem.initVal ⟨n1 + 8, 8⟩ = 0) :
    MemInv (treiber2GA t n0 n1) (Config.init states initMem).mem := by
  refine ⟨fun l hl => ?_, fun w hw => by simp [Config.init] at hw⟩
  rcases hl with rfl | rfl | rfl
  · simp only [Treiber2ValVA, hT0]; simp
  · simp only [Treiber2ValVA, hN0]; simp
  · simp only [Treiber2ValVA, hN1]; simp

section Whole

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot2)]

/-- **The value specification of `pilot2`** in `inv (SLay P) (GV P)`: the
`Safely` invariant of `main_val2`, ending at the end of the text. -/
def pilot2ValSpec (P : Params) : ThreadSpec (SLay P) (GV P) :=
  ThreadSpec.ofSafely (layout pilot2) ((layout pilot2).addrOf pilot2.length)
    (fun x => (x.1.2 = (layout pilot2).addrOf pilot2.length ∧ ∃ _ : Nat, True) ∨ False)
    (fun _ h => h.elim And.left False.elim)

/-- **A `StartP2` start holds the value specification.** -/
theorem pilot2ValSpec_holds {P : Params} {w : Nat} (hw : w < 2) {d9 : BitVec 32} {lo : BitVec 64} {nb : Nat}
    {s : isa.State} (hS : StartP2 P w d9 lo nb s) : (pilot2ValSpec P).Holds s := by
  letI : CodeEnv := ⟨layout pilot2⟩
  exact ⟨hS.exe, hS.endPc, hS.decls, safely_start_of_partialTripleEnv (main_val2 P w hw lo nb).uncount rfl hS.pc
    ⟨0, hS.x30, hS.x21, hS.x27, hS.x28, hS.stack, hS.sp, hS.slot⟩ (by simp)⟩

/-- **The hand-lowered two-thread Treiber client with a `dmem` frame, on the
Promising model, unconditionally** (AArch64, `Arch.armv8`):
`pilot2_promising_of_envGValsBridge` without `hBr` and `hvals`; the start
facts are the stack-frame pilot's plus `hN0`/`hN1` (both links start at `0`). -/
theorem pilot2_promising {t n0 n1 : BitVec 64} {fuel : Nat}
    (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} {lo0 lo1 : BitVec 64} {nb0 nb1 : Nat}
    (h0 : StartP2 (tPD t n0 n1) 0 1 lo0 nb0 s0) (h1 : StartP2 (tPD t n0 n1) 1 2 lo1 nb1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [s0, s1] initMem).mem.initVal ⟨n0 + 8, 8⟩ = 0)
    (hN1 : (Config.init [s0, s1] initMem).mem.initVal ⟨n1 + 8, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg := by
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  have hrel : ∀ (l : Loc), l ≠ (tPD t n0 n1).top → ∀ v, Pred.Pure ((ghost₀ (tPD t n0 n1)).rel l) v :=
    fun l hl v => by rw [ghost₀_rel_ne hl]; exact Pred.emp_pure v
  refine Vals.envGValsBridge_ofSpecs (treiber2GA t n0 n1) (fun _ => pilot2ValSpec (tPD t n0 n1)) Arch.armv8 fuel
    [s0, s1] initMem _ (ghost₀ (tPD t n0 n1)) (TB2D (tPD t n0 n1))
    (Treiber2DFinal n0 n1) (plan (tPD t n0 n1)) (fun _ => layout pilot2)
    (fun _ => (layout pilot2).addrOf pilot2.length) (fun w => postP2 (tPD t n0 n1) w)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) rfl (fun _ => pilot2PureSpec _) ?_
    (memInv_treiber2_init hT0 hN0 hN1) ?_ ?_ cfg hc hf fun rF' g' E' hle hsize hB => ?_
  · rintro (_ | _ | _) s hs <;> cases hs
    · exact pilot2PureSpec_holds (by decide) (hrel _ (Ne.symm (top_dd _ 0))) (hrel _ (hL.top_nd' (by decide)).symm) h0
    · exact pilot2PureSpec_holds (by decide) (hrel _ (Ne.symm (top_dd _ 1))) (hrel _ (hL.top_nd' (by decide)).symm) h1
  · rintro (_ | _ | _) th hth <;> simp [Config.init] at hth <;> subst hth
    · exact pilot2ValSpec_holds (by decide) h0
    · exact pilot2ValSpec_holds (by decide) h1
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

section
attribute [local instance] pLayout2

/-- **Non-vacuity, unconditionally**: `pilot2_promising` (primed beside
the stack-frame pilot's conditional `pilot2_promising_concrete`) at the explorer's
configuration (`pilot2Run`, `Lower/Pilot2Prog.lean`): `top` at `0x1000`, arenas
at `0x2000`/`0x3000`, payloads `1`/`2`, stacks `[0x8000, 0x8040)` and
`[0x9000, 0x9040)`. -/
theorem pilot2_promising_concrete' {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [thread2 0x2000 1 0x8040, thread2 0x3000 2 0x9040] Pilot.initMem) c)
    (hf : c.final = true) : Treiber2DFinal 0x2000 0x3000 c :=
  pilot2_promising (by decide) (by decide) (by decide) (by decide) (by decide)
    (thread2_start _ _ _ _ rfl (by decide) (by decide) (by decide) (heap_far (.inl (by decide))))
    (thread2_start _ _ _ _ rfl (by decide) (by decide) (by decide) (heap_far (.inr (by decide))))
    (by simp only [Config.init_mem]; decide) (by simp only [Config.init_mem]; decide)
    (by simp only [Config.init_mem]; decide) hc hf

end

end Kraken.Promising.Lower.Pilot2

#print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising
#print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising_concrete'
