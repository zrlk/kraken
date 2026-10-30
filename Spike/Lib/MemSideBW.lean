/-
**A memory side with the output's byte step and abort justification set**
(`MemSide.bo`, `MemSide.we`), on any ISA: the rows proved under a memory
side whose `bo` and `we` are weaker (as `MemSide`'s defaults, none) stay rows
under it.

- `MemSide.withBW ms bo we`: `ms` with `bo` and `we` replaced, every other
  field kept;
- `Out.withBW`, `OutS.withBW`, `SegW.withBW`, `SegWS.withBW`: an `Out` row, a
  row at depth and the segments under `ms` are ones under `ms.withBW bo we`
  when `ms.bo` implies `bo` and `ms.we` implies `we` (only `Out.emit` reads
  them); `withBW_of_none`: the case of a memory side with neither;
  `Out.unBW`: the converse at a state that is not a `write(1, …)`.
-/
import Spike.Lib.SegS

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising

/-- **`ms` with the output's byte step `bo` and abort justification `we`**,
every other field kept. -/
def MemSide.withBW {I : ISA} (ms : MemSide I) (bo : I.State → Nat → Ctl → (Ctl → Prop) → Prop)
    (we : I.State → Ctl → Prop) : MemSide I :=
  { ms with bo, we }

section BW

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
  {bo : I.State → Nat → Ctl → (Ctl → Prop) → Prop} {we : I.State → Ctl → Prop}

/-- A system call matched under `ms` is matched under `ms.withBW bo we`
(`SysOk` reads `abortAt` and `pl` only). -/
theorem SysOk.withBW {s : I.State} {c : Ctl} {call : Scc.Sem.Kernel.Call} (h : SysOk p ms s c call) :
    SysOk p (ms.withBW bo we) s c call :=
  h

/-- **An `Out` row under `ms` is one under `ms.withBW bo we`** when `ms`'s
byte step and abort justification imply `bo` and `we`. -/
theorem Out.withBW {X : Frag I} {s : I.State} {c : Ctl} (h : Out p lbl ms X s c)
    (hbo : ∀ s a c Q, ms.bo s a c Q → bo s a c Q) (hwe : ∀ s c, ms.we s c → we s c) :
    Out p lbl (ms.withBW bo we) X s c := by
  cases h with
  | silent s' c' he hr hx => exact .silent s' c' he hr hx
  | choice P t he hs hx => exact .choice P t he hs hx
  | load kl A g x a e ty w he ht hev hv hx htag => exact .load kl A g x a e ty w he ht hev hv hx htag
  | store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb hx htag =>
    exact .store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb hx htag
  | rtStore kr L V s' c' he hrt hm hG hr hx => exact .rtStore kr L V s' c' he hrt hm hG hr hx
  | rtLoad kl L g c' he hrt hm hr hx => exact .rtLoad kl L g c' he hrt hm hr hx
  | rtRmw k L op g c' he hrt hm hr hx => exact .rtRmw k L op g c' he hrt hm hr hx
  | sys K call hK ha hd hok hx => exact .sys K call hK ha hd hok.withBW hx
  | holdLoad kl A g x sa u v e he hx hA hh hX => exact .holdLoad kl A g x sa u v e he hx hA hh hX
  | xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv hX =>
    exact .xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv hX
  | ctrRmw k op g x τ e n he hrt hm hs hh hop hX =>
    exact .ctrRmw k op g x τ e n he hrt hm hs hh hop hX
  | alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX =>
    exact .alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX
  | newStore kr A V s' x a ty e w wold old hN he hm ht hev hu hv hh hold hA hc hX =>
    exact .newStore kr A V s' x a ty e w wold old hN he hm ht hev hu hv hh hold hA hc hX
  | emit K buf n Pw Qw hK ha hd h0 hb hr hq =>
    exact .emit K buf n Pw Qw hK ha hd h0 (fun j hj c1 hp => hbo _ _ _ _ (hb j hj c1 hp)) hr
      (fun c1 h => hwe _ _ (hq c1 h))
  | fence k s' c' he hr hx => exact .fence k s' c' he hr hx

/-- A memory side with no byte step and no abort justification (`MemSide`'s
defaults) is weaker than any. -/
theorem withBW_of_none {X : Frag I} {s : I.State} {c : Ctl} (h : Out p lbl ms X s c)
    (hbo : ∀ s a c Q, ¬ ms.bo s a c Q) (hwe : ∀ s c, ¬ ms.we s c) : Out p lbl (ms.withBW bo we) X s c :=
  h.withBW (fun s a c Q h' => (hbo s a c Q h').elim) fun s c h' => (hwe s c h').elim

/-- **An `OutS` row at depth** under the memory sides `ms` is one under
`(ms ·).withBW bo we`. -/
theorem OutS.withBW {ms : List TermRun.Frame → MemSide I} {X : FragS I} {s : I.State} {c : Ctl}
    {fs : List TermRun.Frame} (h : OutS p lbl ms X s c fs)
    (hbo : ∀ fs s a c Q, (ms fs).bo s a c Q → bo s a c Q) (hwe : ∀ fs s c, (ms fs).we s c → we s c) :
    OutS p lbl (fun fs => (ms fs).withBW bo we) X s c fs := by
  cases h with
  | pre c₁ fs₁ hr h => exact .pre c₁ fs₁ hr (h.withBW (hbo fs₁) (hwe fs₁))
  | frame s' c' fs' he hr hx => exact .frame s' c' fs' he hr hx

/-- **The converse off the output row**: an `Out` row under
`ms.withBW bo we` at a state that is not a `write(1, …)` under `ms`'s kernel
model is one under `ms` (only `Out.emit` reads `bo` and `we`). -/
theorem Out.unBW {X : Frag I} {s : I.State} {c : Ctl} (h : Out p lbl (ms.withBW bo we) X s c)
    (hne : ∀ K, ms.K = some K → K.atSys s = true → ∀ buf n,
      Scc.Sem.Kernel.decode K.nrs (K.nr s) (K.arg s) ≠ some (.write 1 buf n)) :
    Out p lbl ms X s c := by
  cases h with
  | silent s' c' he hr hx => exact .silent s' c' he hr hx
  | choice P t he hs hx => exact .choice P t he hs hx
  | load kl A g x a e ty w he ht hev hv hx htag => exact .load kl A g x a e ty w he ht hev hv hx htag
  | store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb hx htag =>
    exact .store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb hx htag
  | rtStore kr L V s' c' he hrt hm hG hr hx => exact .rtStore kr L V s' c' he hrt hm hG hr hx
  | rtLoad kl L g c' he hrt hm hr hx => exact .rtLoad kl L g c' he hrt hm hr hx
  | rtRmw k L op g c' he hrt hm hr hx => exact .rtRmw k L op g c' he hrt hm hr hx
  | sys K call hK ha hd hok hx => exact .sys K call hK ha hd hok hx
  | holdLoad kl A g x sa u v e he hx hA hh hX => exact .holdLoad kl A g x sa u v e he hx hA hh hX
  | xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv hX =>
    exact .xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv hX
  | ctrRmw k op g x τ e n he hrt hm hs hh hop hX =>
    exact .ctrRmw k op g x τ e n he hrt hm hs hh hop hX
  | alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX =>
    exact .alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX
  | newStore kr A V s' x a ty e w wold old hN he hm ht hev hu hv hh hold hA hc hX =>
    exact .newStore kr A V s' x a ty e w wold old hN he hm ht hev hu hv hh hold hA hc hX
  | emit K buf n Pw Qw hK ha hd => exact (hne K hK ha buf n hd).elim
  | fence k s' c' he hr hx => exact .fence k s' c' he hr hx

/-- **A segment inside `W` closed under `K`** under `ms` is one under
`ms.withBW bo we`. -/
theorem SegW.withBW {W : Frag I} {K : I.State → I.State → Prop} {P Q : Frag I} (h : SegW W K p lbl ms P Q)
    (hbo : ∀ s a c Q, ms.bo s a c Q → bo s a c Q) (hwe : ∀ s c, ms.we s c → we s c) :
    SegW W K p lbl (ms.withBW bo we) P Q :=
  let ⟨inv, hP, hW, hcl⟩ := h
  ⟨inv, hP, hW, fun s c hi => ⟨fun hk => ((hcl s c hi).1 hk).withBW hbo hwe, (hcl s c hi).2⟩⟩

/-- **A segment at depth** under the memory sides `ms` is one under
`(ms ·).withBW bo we`. -/
theorem SegWS.withBW {ms : List TermRun.Frame → MemSide I} {W : FragS I} {K : I.State → I.State → Prop}
    {P Q : FragS I} (h : SegWS W K p lbl ms P Q)
    (hbo : ∀ fs s a c Q, (ms fs).bo s a c Q → bo s a c Q) (hwe : ∀ fs s c, (ms fs).we s c → we s c) :
    SegWS W K p lbl (fun fs => (ms fs).withBW bo we) P Q :=
  let ⟨inv, hP, hW, hcl⟩ := h
  ⟨inv, hP, hW, fun s c fs hi => ⟨fun hk => ((hcl s c fs hi).1 hk).withBW hbo hwe, (hcl s c fs hi).2⟩⟩

end BW

end Spike.Lib
