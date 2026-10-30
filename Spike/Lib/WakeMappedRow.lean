/-
**A row's instruction touches only mapped locations** (generic in the ISA
and the kernel state): the per-instruction rows (`Out`, `OutL`, `OutT`)
access either a runtime location, mapped by the memory side (`MemSide.mp`),
or a label word through the source's pointer (`load`, `store`, `ldSt`,
`holdLoad`, `xchgStore`), mapped by `LabMapped`, a fact of the source
control alone; every other row's step has no access (`silent`, `choice`,
`alloc`, `fnc`) or is a system call (`sys`, `emit`, `texit`), excluded
off a system call.

- `LabPtr c sa`: `c` accesses the word at `sa` through an untagged
  locative (a load, a store or an exchange site);
- `LabMapped lbl K c`: every such word's address under `lbl` is mapped in
  `K` for reading and writing;
- `noTouch_silent`: a silent tree touches nothing;
- `noTouch_of_out`, `noTouch_of_outL`, `noTouch_of_outT`: a row's step
  touches no location `K` leaves unmapped, given the memory side's `mp`
  is mapped in `K` (`hmp`), the state is off a system call of the kernel
  model (`hat`) and `LabMapped`;
- `hM_of`, `hW_of`: `WakeMapped.hmapped_of`'s premises `hM`, `hW` from
  main's and the worker's rows (`MSide.closed`, `WSide.closed`), their
  memory sides' `mp` mapped in `K0` and their label words mapped
  (`LabMapped`) at every invariant state.
-/
import Spike.Lib.SegThr
import Spike.Lib.A64Consumer
import Spike.Lib.WakeM0
import Spike.Lib.WakeW1

namespace Spike.Lib.WakeMappedRow

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Lower (SilentTree)
open Scc.Sem (ValRep)

/-- **`c` accesses the word at `sa` through an untagged locative**: a load
or store term whose pointer evaluates to one word `.loc sa 0`, or an
exchange site at `sa`. -/
def LabPtr (c : Ctl) (sa : WeakMem.Address) : Prop :=
  (∃ x a e ty w, (c.term = .let_ x (.load true a) e ∨ ∃ b, c.term = .let_ x (.store true a b none) e) ∧
    TermRun.evalAt c.env a = some (ty, [w]) ∧ w.val = .loc sa 0) ∨
  ∃ x u v e, XchgSite c x sa u v e

/-- **The source's label words are mapped** in `K`: every word `c`
accesses through an untagged locative (`LabPtr`), at the address its
locative represents under `lbl`, is mapped for reading and writing. -/
def LabMapped (lbl : WeakMem.AllocLabel → Option Nat) (K : Scc.Sem.Kernel.KState) (c : Ctl) : Prop :=
  ∀ sa (A : BitVec 64), LabPtr c sa → ValRep lbl (.loc sa 0) A.toNat → ∀ wr,
    Scc.Sem.Kernel.mapped K wr ⟨A, 8⟩ = true

/-- **A silent tree touches nothing.** -/
theorem noTouch_silent {σ : Type} {P : σ → Prop} {p : Loc → Bool → Prop} :
    ∀ {t : EvTree σ}, SilentTree P t → ¬ Scc.Sem.Kernel.Touches p t
  | .done _, _, h => nomatch h
  | .fault _, hs, _ => hs.elim
  | .choose _ _, hs, h => by
    cases h with
    | choose i h => exact noTouch_silent (hs.2 i) h
  | .load .., hs, _ => hs.elim
  | .store .., hs, _ => hs.elim
  | .rmw .., hs, _ => hs.elim
  | .fence .., hs, _ => hs.elim

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I} {X : Frag I}
  {s : I.State} {c : Ctl} {K : Scc.Sem.Kernel.KState}

local notation "Unm" K => fun (l : Loc) (w : Bool) => Scc.Sem.Kernel.mapped K w l = false

/-- An access at a mapped location, every continuation a leaf, touches
nothing unmapped. -/
private theorem noTouch_load {kl : Kraken.LoadKind} {L : Loc} {g : Val → I.State}
    (hm : Scc.Sem.Kernel.mapped K false L = true) :
    ¬ Scc.Sem.Kernel.Touches (Unm K) (.load kl false L fun v => .done (g v)) := fun h => by
  cases h with
  | load h => rw [hm] at h; cases h
  | loadRet _ h => cases h

private theorem noTouch_store {kr : Kraken.StoreKind} {L : Loc} {V : Val} {s' : I.State}
    (hm : Scc.Sem.Kernel.mapped K true L = true) :
    ¬ Scc.Sem.Kernel.Touches (Unm K) (.store kr false L V fun _ => .done s') := fun h => by
  cases h with
  | store h => rw [hm] at h; cases h
  | storeRet _ h => cases h

private theorem noTouch_rmw {k : Kraken.RmwKind} {L : Loc} {op : Val → Option Val} {g : Val → I.State}
    (hm : Scc.Sem.Kernel.mapped K true L = true) :
    ¬ Scc.Sem.Kernel.Touches (Unm K) (.rmw k false L op fun v => .done (g v)) := fun h => by
  cases h with
  | rmw h => rw [hm] at h; cases h
  | rmwRet _ h => cases h

/-- **An `Out` row's step touches no location `K` leaves unmapped**: its
runtime accesses are mapped in `K` (`hmp`), the state is off a system call
of the kernel model (`hat`), and its label words are mapped (`LabMapped`). -/
theorem noTouch_of_out (h : Out p lbl ms X s c)
    (hmp : ∀ L w, ms.mp L w → Scc.Sem.Kernel.mapped K w L = true)
    (hat : ∀ K', ms.K = some K' → K'.atSys s = false) (hlab : LabMapped lbl K c)
    {e : EvTree I.State} (he : I.exec s = some e) : ¬ Scc.Sem.Kernel.Touches (Unm K) e := by
  cases h with
  | silent s' c' hx _ _ => rw [hx] at he; cases he; nofun
  | choice P t hx hs _ => rw [hx] at he; cases he; exact noTouch_silent hs
  | load kl A g x a e' ty w hx ht hev hv _ htag =>
    rw [hx] at he; cases he
    obtain ⟨sa, hsa⟩ := htag
    exact noTouch_load (hlab sa A (.inl ⟨x, a, e', ty, w, .inl ht, hev, hsa⟩) (hsa ▸ hv) false)
  | store kr A V s' x a b e' ty tb w wb hx ht hev hv _ _ _ htag =>
    rw [hx] at he; cases he
    obtain ⟨sa, hsa⟩ := htag
    exact noTouch_store (hlab sa A (.inl ⟨x, a, e', ty, w, .inr ⟨b, ht⟩, hev, hsa⟩) (hsa ▸ hv) true)
  | rtStore kr L V s' c' hx _ hm => rw [hx] at he; cases he; exact noTouch_store (hmp _ _ hm)
  | rtLoad kl L g c' hx _ hm => rw [hx] at he; cases he; exact noTouch_load (hmp _ _ hm)
  | rtRmw k L op g c' hx _ hm => rw [hx] at he; cases he; exact noTouch_rmw (hmp _ _ hm)
  | sys K' call hK ha => rw [hat K' hK] at ha; cases ha
  | holdLoad kl A g x sa u v e' hx hs hA =>
    rw [hx] at he; cases he
    exact noTouch_load (hlab sa A (.inr ⟨x, u, v, e', hs⟩) hA false)
  | xchgStore kr A V s' x sa u v e' tv wv wold hx hs hA =>
    rw [hx] at he; cases he
    exact noTouch_store (hlab sa A (.inr ⟨x, u, v, e', hs⟩) hA true)
  | ctrRmw k op g x τ e' n hx _ hm => rw [hx] at he; cases he; exact noTouch_rmw (hmp _ _ hm)
  | alloc s' A x a τ e' ta ws k wold old us hx => rw [hx] at he; cases he; nofun
  | newStore kr A V s' x a t e' w wold old _ hx hm => rw [hx] at he; cases he; exact noTouch_store (hmp _ _ hm)
  | emit K' buf n Pw Qw hK ha => rw [hat K' hK] at ha; cases ha
  | fence k s' c' hx =>
    rw [hx] at he; cases he
    intro h
    cases h with
    | fence h => cases h

/-- **An `OutL` row's step touches no location `K` leaves unmapped**
(`noTouch_of_out`; the load-or-stutter row loads a label word). -/
theorem noTouch_of_outL (h : OutL p lbl ms X s c)
    (hmp : ∀ L w, ms.mp L w → Scc.Sem.Kernel.mapped K w L = true)
    (hat : ∀ K', ms.K = some K' → K'.atSys s = false) (hlab : LabMapped lbl K c)
    {e : EvTree I.State} (he : I.exec s = some e) : ¬ Scc.Sem.Kernel.Touches (Unm K) e := by
  cases h with
  | out h => exact noTouch_of_out h hmp hat hlab he
  | ldSt kl A g x a e' ty w V hx ht hev hv _ _ htag =>
    rw [hx] at he; cases he
    obtain ⟨sa, hsa⟩ := htag
    exact noTouch_load (hlab sa A (.inl ⟨x, a, e', ty, w, .inl ht, hev, hsa⟩) (hsa ▸ hv) false)

/-- **An `OutT` row's step touches no location `K` leaves unmapped**
(`noTouch_of_outL`; the unpark's RMW is a runtime access, the thread's exit
a system call, a fence over a leaf touches nothing). -/
theorem noTouch_of_outT (h : OutT p lbl ms X s c)
    (hmp : ∀ L w, ms.mp L w → Scc.Sem.Kernel.mapped K w L = true)
    (hat : ∀ K', ms.K = some K' → K'.atSys s = false) (hlab : LabMapped lbl K c)
    {e : EvTree I.State} (he : I.exec s = some e) : ¬ Scc.Sem.Kernel.Touches (Unm K) e := by
  cases h with
  | outL h => exact noTouch_of_outL h hmp hat hlab he
  | unpk k A B op g x a e' ty jw hx _ hm => rw [hx] at he; cases he; exact noTouch_rmw (hmp _ _ hm)
  | texit K' a hK ha => rw [hat K' hK] at ha; cases ha
  | fnc k s' c' hx =>
    rw [hx] at he; cases he
    intro h
    cases h with
    | fence h => cases h

/-- **`hmapped_of`'s `hM`** from main's rows: its memory sides under the
model `abi`, their `mp` mapped in `K0`, the label words of every invariant
state mapped in `K0`. -/
theorem hM_of {ι : Type} {M : WakeM0.MSide ι} {Λ : Scc.Sem.Layout}
    (hK : ∀ w, (M.ms w).K = some Scc.Sem.A64.abi)
    (hmp : ∀ w L wr, (M.ms w).mp L wr → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) wr L = true)
    (hlab : ∀ w s c, M.Mi w s c → LabMapped (M.lbl w) (Spike.Lib.A64Consumer.K0 Λ) c) :
    ∀ w s c, M.Mi w s c → Scc.Sem.A64.abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
      ¬ Scc.Sem.Kernel.Touches (fun l w => Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) w l = false) e :=
  fun w s c hi hs e he => noTouch_of_outL (M.closed w s c hi) (hmp w)
    (fun K' hK' => by rw [hK w] at hK'; cases hK'; exact hs) (hlab w s c hi) he

/-- **`hmapped_of`'s `hW`** from the worker's rows (as `hM_of`). -/
theorem hW_of {ι : Type} {D : WakeW1.WSide ι} {Λ : Scc.Sem.Layout}
    (hK : ∀ w, (D.ms w).K = some Scc.Sem.A64.abi)
    (hmp : ∀ w L wr, (D.ms w).mp L wr → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) wr L = true)
    (hlab : ∀ w s c, D.Wi w s c → LabMapped (D.lbl w) (Spike.Lib.A64Consumer.K0 Λ) c) :
    ∀ w s c, D.Wi w s c → Scc.Sem.A64.abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
      ¬ Scc.Sem.Kernel.Touches (fun l w => Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) w l = false) e :=
  fun w s c hi hs e he => noTouch_of_outT (D.closed w s c hi) (hmp w)
    (fun K' hK' => by rw [hK w] at hK'; cases hK'; exact hs) (hlab w s c hi) he

/-- info: 'Spike.Lib.WakeMappedRow.hW_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hW_of

/-- info: 'Spike.Lib.WakeMappedRow.noTouch_of_outT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms noTouch_of_outT

end Spike.Lib.WakeMappedRow
