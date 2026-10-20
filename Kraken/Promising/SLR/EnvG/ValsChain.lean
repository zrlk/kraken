/-
**Part 3 of 4: Theorem 1′ over `Erase ∧ MemInv G`** (route (c2)). ISA-neutral. No chain
edit.

The existing chain is generic in the erasure: `theorem1IIPureXS'` at
`Er := Erase ∧ MemInvX G`, step guard `StepGuard.ful`, with `ChainExt` from
`chainExt_X` (whose `XPromiseLaw` is `MemInv.append`). Its remaining input,
`PromiseFresh'` (an unfulfilled promise of a reachable configuration is a `G`
value), comes from the per-thread value specifications `J` through
`configInv_reachable`.

Contents: `memInvX_promiseLaw`, `stepPreserves_of_allInv`,
`promiseFresh_of_allInv`, **`theorem1FChainV`** and its adequacy form
`final_of_chainV` (the ISA layers supply `NTFree` and `PromisePure`).
-/
import Kraken.Promising.SLR.EnvG.ValsToken

namespace Kraken.Promising.SLR.EnvG.Vals

open Kraken Kraken.Promising Kraken.Promising.Sim Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

variable {I : ISA}

/-- `MemInv G` is preserved by promising a `G` message. -/
theorem memInvX_promiseLaw (G : Loc → Val → Prop) :
    XPromiseLaw (I := I) (MemInvX G) (fun _ w => G w.loc w.val) :=
  fun _ _ _ _ _ _ _ _ _ hX hG => hX.append hG

/-- Per-thread tree laws give `StepPreserves`. -/
theorem stepPreserves_of_allInv {A : Arch} {G : Loc → Val → Prop} {J : Nat → I.State → Prop}
    (hJ : ∀ tid st tree, J tid st → I.exec st = some tree → tree.AllInv G (J tid)) : StepPreserves A G J :=
  fun tid _ _ _ _ hj hm hst ho => stepOne_allInv A hst ho (fun tree hex => hJ tid _ tree hj hex) hm

/-- **`PromiseFresh'` for `G`** from the per-thread value specifications: a
promise is a step from a reachable configuration, whose memory satisfies
`MemInv G` by `configInv_reachable`. -/
theorem promiseFresh_of_allInv {A : Arch} [I.LawfulState] {fuel : Nat} {G : Loc → Val → Prop}
    {J : Nat → I.State → Prop} (hJ : ∀ tid st tree, J tid st → I.exec st = some tree → tree.AllInv G (J tid))
    {states : List I.State} {initMem : List (Loc × Val)} (h0 : ConfigInv G J (Config.init states initMem))
    (GP : PrepayGuard I) :
    PromiseFresh' GP A fuel states initMem (fun _ w => G w.loc w.val) := by
  intro π h0π _ J' hJ' j t pw _ _ hJ1 _
  have hc := configInv_reachable (stepPreserves_of_allInv hJ) h0 (h0π ▸ π.reachable (J' + 1) (by omega))
  rw [hJ1] at hc
  exact hc.1.2 _ (by simp [Config.withThread, Memory.append])

/-- **Theorem 1′ for `NPSafeF` tokens over `Erase ∧ MemInv G`**, with the
value side given by per-thread value specifications `J` (tree law `hJ`, `J`
and `MemInv G` at the start: `h0`). The virtual configuration also satisfies
`MemInv G`. -/
theorem theorem1FChainV [I.LawfulState] (A : Arch) (fuel : Nat) (G : Loc → Val → Prop)
    (J : Nat → I.State → Prop) (hJ : ∀ tid st tree, J tid st → I.exec st = some tree → tree.AllInv G (J tid))
    (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val)) (rF : Nat → Res)
    (g : Ghost) (hNT : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (E : Erase rF g (fun _ => False) (Config.init states initMem)) (h0 : ConfigInv G J (Config.init states initMem))
    (hp : ∀ ts, ts ∉ g.pend) (hpure : PromisePure' G₀ A fuel states initMem g.rel)
    (hs : ∀ tid, tid < states.length → ∀ n m,
      NPSafeF (modelX I (MemInvX G)) A B tid n m True (Config.init states initMem) (rF tid) g)
    (c : Config I) (hc : Reachable A fuel (Config.init states initMem) c) (hl : c.Live A fuel) :
    ∃ v rF' g', c.VirtualOfG GRF A v ∧ Erase rF' g' (fun _ => False) v ∧ MemInv G v.mem ∧ g.Le g' ∧
      ∀ tid, v.Done tid → B v (rF' tid) g' := by
  have hfresh := promiseFresh_of_allInv (A := A) (fuel := fuel) hJ h0 G₀
  obtain ⟨v, rF', g', hv, ⟨E', hX'⟩, hle, hB⟩ :=
    theorem1IIPureXS' (S := StepGuard.ful _) (chainExt_X (memInvX_promiseLaw G)) guardOK_G₀ guardOK_GRF
      (fun _ _ _ _ _ h => G₀_le_GRF h) (k2OK_K2₀ _) A fuel B states initMem rF g hNT ⟨E, h0.1⟩ hp
      (fun π h0 hf J hJ j t pw ht hw hJ1 hn =>
        ⟨hpure π h0 hf J hJ j t pw ht hw hJ1 hn, hfresh π h0 hf J hJ j t pw ht hw hJ1 hn⟩)
      (fun tid htid n m => Eq.mp (npSafeF_eq_apply (modelX I (MemInvX G)) A B tid n m True _ _ _) (hs tid htid n m))
      c hc hl
  exact ⟨v, rF', g', hv, E', hX', hle, hB⟩

/-- **Adequacy from `theorem1FChainV`** (`final_of_virtual`): a final
reachable configuration satisfies `Φ` when `Φ` follows from clean erasure, a
world above `g₀`, the thread count and `B` at every halted thread. The value
side is `MemInv G` of the initial memory, `J` at the initial states and the
tree law; `NTFree` and `PromisePure` are the ISA layer's. -/
theorem final_of_chainV [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config I → Res → Ghost → Prop}
    {Φ : Config I → Prop} (G : Loc → Val → Prop) (J : Nat → I.State → Prop)
    (hJ : ∀ tid st tree, J tid st → I.exec st = some tree → tree.AllInv G (J tid))
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (hm0 : MemInv G (Config.init states initMem).mem) (h0v : ∀ tid s, states[tid]? = some s → J tid s)
    (hpure : PromisePure A fuel states initMem g₀.rel)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeF (modelX I (MemInvX G)) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config I} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  have hci : ConfigInv G J (Config.init states initMem) := ⟨hm0, fun tid t ht => by
    obtain ⟨s, hs, rfl⟩ := Config.init_get?_thread ht
    exact h0v tid s hs⟩
  obtain ⟨v, rF', g', hv, E', -, hle, hB⟩ :=
    theorem1FChainV A fuel G J hJ B states initMem rF g₀ hH hE hci hpend hpure hsafe c hc ⟨c, .refl c, hf⟩
  exact final_of_virtual hc hf ⟨v, rF', g', hv, E', hle, hB⟩ hfin

end Kraken.Promising.SLR.EnvG.Vals

#print axioms Kraken.Promising.SLR.EnvG.Vals.final_of_chainV
