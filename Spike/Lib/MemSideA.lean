/-
**Rows away from a buffer allocation under a memory side with the arena**,
on any ISA: an `Out` row reads the arena's fields (`MemSide.heap`, `ctr`,
`units`, `off`, `cells`) and the allocation fragment (`MemSide.xa`) only in
its counter add and allocation rows (`Out.ctrRmw`, `Out.alloc`), both at a
`let x = newBuf a τ in e`; and the output's byte step and abort
justification (`MemSide.bo`, `we`) only in its output row (`Out.emit`). So a
row proved under a memory side with no arena (as `msOfS`, `MemSide`'s
defaults) at a control that is no buffer allocation is one under any memory
side agreeing on the other fields, with a byte step and abort justification
implied by the first's (as an arena one, `msOfA`/`msOfAB`).

- `NoNewBuf c`: the control is no buffer allocation.
- `Out.toA`, `OutS.toA`, `SegWS.toA`: an `Out` row, a row at depth and a
  segment at depth carried to such a memory side, the controls the rows are
  taken at (from `W`'s pairs, after a frame run) being no buffer allocation.
-/
import Spike.Lib.SegS

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising

/-- **The control is no buffer allocation** (`Out.ctrRmw`'s and
`Out.alloc`'s term). -/
def NoNewBuf (c : Ctl) : Prop := ∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e

section ToA

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}

/-- **An `Out` row at a control that is no buffer allocation** under `ms` is
one under `ms'` agreeing with `ms` on every field but the arena's (`heap`,
`ctr`, `units`, `off`, `cells`) and the allocation fragment (`xa`), whose
byte step and abort justification (`bo`, `we`) are implied by `ms`'s. -/
theorem Out.toA {ms ms' : MemSide I} {X : Frag I} {s : I.State} {c : Ctl} (h : Out p lbl ms X s c)
    (hrd : ms'.rd = ms.rd) (hrt : ms'.rt = ms.rt) (hK : ms'.K = ms.K) (hG : ms'.G = ms.G)
    (hown : ms'.own = ms.own) (hmp : ms'.mp = ms.mp) (hab : ms'.abortAt = ms.abortAt) (hpl : ms'.pl = ms.pl)
    (hbo : ∀ s a c Q, ms.bo s a c Q → ms'.bo s a c Q) (hwe : ∀ s c, ms.we s c → ms'.we s c)
    (hnb : NoNewBuf c) (hpub : ms.pub → ms'.pub := by first | exact id | exact False.elim)
    (hnn : ¬ ms.newOk := by first | exact id | exact fun h => h) : Out p lbl ms' X s c := by
  obtain ⟨rd, rt, K, G, heap, ctr, units, off, cells, own, mp, ab, pl, xa, bo, we, lo, pub, newOk⟩ := ms
  obtain ⟨rd', rt', K', G', heap', ctr', units', off', cells', own', mp', ab', pl', xa', bo', we', lo', pub',
    newOk'⟩ := ms'
  dsimp only at hrd hrt hK hG hown hmp hab hpl hbo hwe
  subst hrd hrt hK hG hown hmp hab hpl
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
  | ctrRmw k op g x τ e n he hrt hm hs =>
    exact (hs.elim (fun ⟨a, _, _, ht, _⟩ => hnb x a τ e ht) fun ⟨hN, _⟩ => hnn hN).elim
  | alloc s' A x a τ e ta ws k wold old us he ht => exact (hnb x a τ e ht).elim
  | newStore _ _ _ _ _ _ _ _ _ _ _ hN => exact (hnn hN).elim
  | emit K buf n Pw Qw hK ha hd h0 hb hr hq =>
    exact .emit K buf n Pw Qw hK ha hd h0 (fun j hj c1 hp => hbo _ _ _ _ (hb j hj c1 hp)) hr
      (fun c1 h => hwe _ _ (hq c1 h))
  | fence k s' c' he hr hx => exact .fence k s' c' he (hr.mono hpub) hx

/-- **An `OutS` row at depth** whose row control (after the frame run) is
no buffer allocation is one under `ms'` (`Out.toA` at every depth). -/
theorem OutS.toA {ms ms' : List TermRun.Frame → MemSide I} {X : FragS I} {s : I.State} {c : Ctl}
    {fs : List TermRun.Frame} (h : OutS p lbl ms X s c fs)
    (hrd : ∀ fs, (ms' fs).rd = (ms fs).rd) (hrt : ∀ fs, (ms' fs).rt = (ms fs).rt)
    (hK : ∀ fs, (ms' fs).K = (ms fs).K) (hG : ∀ fs, (ms' fs).G = (ms fs).G)
    (hown : ∀ fs, (ms' fs).own = (ms fs).own) (hmp : ∀ fs, (ms' fs).mp = (ms fs).mp)
    (hab : ∀ fs, (ms' fs).abortAt = (ms fs).abortAt) (hpl : ∀ fs, (ms' fs).pl = (ms fs).pl)
    (hbo : ∀ fs s a c Q, (ms fs).bo s a c Q → (ms' fs).bo s a c Q)
    (hwe : ∀ fs s c, (ms fs).we s c → (ms' fs).we s c)
    (hnb : ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) → NoNewBuf c₁)
    (hpub : ∀ fs, (ms fs).pub → (ms' fs).pub := by first | exact fun _ => id | exact fun _ => False.elim)
    (hnn : ∀ fs, ¬ (ms fs).newOk := by first | exact fun _ => id | exact fun _ h => h) :
    OutS p lbl ms' X s c fs := by
  cases h with
  | pre c₁ fs₁ hr h =>
    exact .pre c₁ fs₁ hr (h.toA (hrd fs₁) (hrt fs₁) (hK fs₁) (hG fs₁) (hown fs₁) (hmp fs₁) (hab fs₁) (hpl fs₁)
      (hbo fs₁) (hwe fs₁) (hnb c₁ fs₁ hr) (hpub fs₁) (hnn fs₁))
  | frame s' c' fs' he hr hx => exact .frame s' c' fs' he hr hx

/-- **A segment at depth** under `ms` is one under `ms'` (`OutS.toA`) when
no control a frame run reaches from a pair of `W` is a buffer allocation. -/
theorem SegWS.toA {ms ms' : List TermRun.Frame → MemSide I} {W : FragS I} {K : I.State → I.State → Prop}
    {P Q : FragS I} (h : SegWS W K p lbl ms P Q)
    (hrd : ∀ fs, (ms' fs).rd = (ms fs).rd) (hrt : ∀ fs, (ms' fs).rt = (ms fs).rt)
    (hK : ∀ fs, (ms' fs).K = (ms fs).K) (hG : ∀ fs, (ms' fs).G = (ms fs).G)
    (hown : ∀ fs, (ms' fs).own = (ms fs).own) (hmp : ∀ fs, (ms' fs).mp = (ms fs).mp)
    (hab : ∀ fs, (ms' fs).abortAt = (ms fs).abortAt) (hpl : ∀ fs, (ms' fs).pl = (ms fs).pl)
    (hbo : ∀ fs s a c Q, (ms fs).bo s a c Q → (ms' fs).bo s a c Q)
    (hwe : ∀ fs s c, (ms fs).we s c → (ms' fs).we s c)
    (hnb : ∀ s c fs, W s c fs → ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) → NoNewBuf c₁)
    (hpub : ∀ fs, (ms fs).pub → (ms' fs).pub := by first | exact fun _ => id | exact fun _ => False.elim)
    (hnn : ∀ fs, ¬ (ms fs).newOk := by first | exact fun _ => id | exact fun _ h => h) :
    SegWS W K p lbl ms' P Q :=
  let ⟨inv, hP, hW, hcl⟩ := h
  ⟨inv, hP, hW, fun s c fs hi => ⟨fun hk => ((hcl s c fs hi).1 hk).toA hrd hrt hK hG hown hmp hab hpl hbo hwe
    (hnb s c fs (hW s c fs hi)) hpub hnn, (hcl s c fs hi).2⟩⟩

end ToA

end Spike.Lib
