import WeakCore.TermFreshU
import WeakCore.TermSpawnGlobM
/-!
# TermFreshUSpawn — `FreshU` across a mid-run spawn (the unborn range shrinks by the kid's stripe)
-/
namespace TermFreshU
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain TermSpawnMid
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **Mid-run spawn.** Same width `N`, same `lbase`, same memory; `EgK` changes only `fpOf`; the kid's
credits are zero.  (Its stripe `c.ths.size` leaves the unborn range; it is `hU`/`hOwnU` of `sysInvN_spawnMid`.) -/
theorem freshU_spawnT {N : Nat} {Eg : GEnv} {c : Cfg} {Tot HP : Nat → Res} {HS : Res} {cr : Nat → Ts → Res}
    {i : Nat} {th par kid : TTh} (hth : c.ths[i]? = some th) (hpp : par.promises = th.promises)
    (hkp : kid.promises = []) (h : FreshU N Eg c Tot HP HS cr) :
    FreshU N (EgK Eg c) (spawnT c i par kid) (extZ Tot c.ths.size) (extZ HP c.ths.size) HS
      (extZT cr c.ths.size) := by
  intro q j hq hqN
  rw [spawnT_size] at hq
  obtain ⟨⟨f1, f2, f3, f4, f5⟩, h2, h3⟩ := h q j (Nat.le_of_succ_le hq) hqN
  exact ⟨⟨f1, f2, f3, f4, f5⟩, TermSpawnGlobM.ownZ_spawnT hth hpp hkp h2, h3⟩

/-- `hU`/`hOwnU` of `sysInvN_spawnMid` from `FreshU` at the post width (`N := (spawnT …).ths.size` pre-M0;
on M0 `N := c.n` and `hcap : c.ths.size < c.n`). -/
theorem kid_of_freshU {N : Nat} {Eg : GEnv} {c : Cfg} {Tot HP : Nat → Res} {HS : Res} {cr : Nat → Ts → Res}
    (hcap : c.ths.size < N) (h : FreshU N Eg c Tot HP HS cr) (q : Nat) :
    FreshX Eg c (freshLabel c.lbase N c.ths.size q) ∧ OwnZ c Tot HP HS cr (freshLabel c.lbase N c.ths.size q) :=
  h c.ths.size q (Nat.le_refl _) hcap

end TermFreshU

#print axioms TermFreshU.freshU_spawnT
#print axioms TermFreshU.kid_of_freshU
