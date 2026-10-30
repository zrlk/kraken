/-
**An unmapped range stays unmapped across a segment** (AArch64): a segment
whose environment moves keep a range `r` unmapped (`A64Consumer.Unowned`)
carries `WideSt ∧ Unowned r` from its start to its exits.

Off the transfer sites, no step grows the private memory's domain. Every
leaf of a certified instruction keeps it (`DomA64.domHyps.exec`), and so do
the allocation rows' `xa` states (`Out.alloc`, `Out.newStore`), which are
such leaves. A system call's resumptions and the output row's returns keep
the private memory exactly (`owned_sys`, `DomHyps.ret`). No row needs a
premise beyond `WideSt`.

- `U`: `WideSt ∧ Unowned r`;
- `exec_un`, `certSuccs_un`: one step keeps `U r`;
- `unXa`: the `xa` exit additionally assuming `U r`;
- `out_un`: one row of `Out` keeps `U r`;
- `SegW.keepUn`: the segment with `U r` conjoined at the start and at every
  exit;
- `take_un`: the take of a range disjoint from `r` keeps `U r`.
-/
import Spike.Lib.A64KeepTP
import Spike.Lib.A64OwnedCopy
import Spike.Lib.A64OwnedMono

namespace Spike.Lib.A64.KeepUn

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Cert.WideA64
open Spike.Lib.A64.KeepTP Spike.Lib.A64Consumer

/-- **The range `r` is unmapped** in a wide state. -/
abbrev U (r : Range) (s : State) : Prop := WideSt s ∧ Unowned r s

/-- A predicate of every leaf is a `TAll`. -/
theorem tall_of_leaf {σ : Type} {Q : σ → Prop} :
    ∀ t : EvTree σ, (∀ s, TreeLeaf t s → Q s) → TAll Q t
  | .done s, h => h s rfl
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => tall_of_leaf (k i) fun s hs => h s ⟨i, hs⟩
  | .load _ _ _ ret, h => fun v => tall_of_leaf (ret v) fun s hs => h s ⟨v, hs⟩
  | .store _ _ _ _ ret, h => fun b => tall_of_leaf (ret b) fun s hs => h s ⟨b, hs⟩
  | .rmw _ _ _ _ ret, h => fun v => tall_of_leaf (ret v) fun s hs => h s ⟨v, hs⟩
  | .fence _ ret, h => fun u => tall_of_leaf (ret u) fun s hs => h s ⟨u, hs⟩

/-- **An instruction keeps `r` unmapped** (`DomHyps.exec`). -/
theorem exec_un {r : Range} {s : State} (hs : U r s) {tr : EvTree State} (he : isaLSE2.exec s = some tr) :
    TAll (U r) tr :=
  tall_of_leaf tr fun _ hl =>
    have h := Scc.Cert.DomA64.domHyps.exec _ _ _ hs.1 he hl
    ⟨h.1, (unowned_of_dom h.2).2 hs.2⟩

/-- **A system call's resumptions keep `r` unmapped.** -/
theorem certSuccs_un {r : Range} {s : State} (hs : U r s) {call : Kernel.Call} :
    ∀ s' ∈ Kernel.certSuccs Scc.Sem.A64.abi s call, U r s' := by
  intro s' hm
  refine ⟨wideSt_soloLeaf hs.1 (Kernel.certSuccs_soloLeaf hm), ?_⟩
  have hd : s'.st.1.dmem = s.st.1.dmem := by
    unfold Kernel.certSuccs at hm
    split at hm
    · cases hm with
      | head => rfl
      | tail _ h => cases h
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp hm; rfl
  exact (unowned_of_dom fun a => by rw [hd]).2 hs.2

/-- **`ms` with every allocation landing asked only with `r` unmapped.** -/
def unXa (ms : MemSide isaLSE2) (r : Range) : MemSide isaLSE2 :=
  { ms with xa := fun l b n s c => U r s → ms.xa l b n s c }

/-- **One instruction keeps `r` unmapped**: what it does under `unXa ms r`
from a state with `r` unmapped it does under `ms` with `r` unmapped in the
fragment it lands in. -/
theorem out_un {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {X : Frag isaLSE2} {s : State} {c : Ctl} {r : Range}
    (hK : ms.K = some Scc.Sem.A64.abi) (hs : U r s)
    (h : Out p lbl (unXa ms r) X s c) : Out p lbl ms (fun s c => X s c ∧ U r s) s c := by
  have hT : ∀ tr, isaLSE2.exec s = some tr → TAll (U r) tr := fun tr he => exec_un hs he
  cases h with
  | silent s' c' he hr hx => exact .silent s' c' he hr ⟨hx, hT _ he⟩
  | choice P tr he hst hl =>
    refine .choice (fun s' => P s' ∧ U r s') tr he (silent_and hst (hT _ he)) fun s' hp => ?_
    obtain ⟨c', hr, hx⟩ := hl s' hp.1
    exact ⟨c', hr, hx, hp.2⟩
  | load kl A g x a e ty w he h1 h2 h3 h4 h5 =>
    exact .load kl A g x a e ty w he h1 h2 h3 (fun v w' hr hv => ⟨h4 v w' hr hv, hT _ he v⟩) h5
  | store kr A V s' x a b e ty tb w wb he h1 h2 h3 h4 h5 h6 h7 =>
    exact .store kr A V s' x a b e ty tb w wb he h1 h2 h3 h4 h5 ⟨h6, hT _ he true⟩ h7
  | rtStore kr L V s' c' he h1 h2 h3 hr hx => exact .rtStore kr L V s' c' he h1 h2 h3 hr ⟨hx, hT _ he true⟩
  | rtLoad kl L g c' he h1 h2 hr hx =>
    exact .rtLoad kl L g c' he h1 h2 hr fun v hG ho => ⟨hx v hG ho, hT _ he v⟩
  | rtRmw k L op g c' he h1 h2 hr hx =>
    exact .rtRmw k L op g c' he h1 h2 hr fun old hG ho => ⟨(hx old hG ho).1, (hx old hG ho).2, hT _ he old⟩
  | sys K' call hK' hat hd hok hsc =>
    have hK2 : ms.K = some K' := hK'
    rw [hK] at hK2
    cases hK2
    refine .sys _ call hK hat hd hok fun s' hm => ?_
    obtain ⟨c', hr, hx⟩ := hsc s' hm
    exact ⟨c', hr, hx, certSuccs_un hs s' hm⟩
  | holdLoad kl A g x sa u v e he h1 h2 h3 h4 =>
    exact .holdLoad kl A g x sa u v e he h1 h2 h3 fun r w' hr hv => ⟨h4 r w' hr hv, hT _ he r⟩
  | xchgStore kr A V s' x sa u v e tv wv wold he h1 h2 h3 h4 h5 h6 =>
    exact .xchgStore kr A V s' x sa u v e tv wv wold he h1 h2 h3 h4 h5 ⟨h6, hT _ he true⟩
  | ctrRmw k op g x τ e n he h1 h2 h3 h4 h5 h6 =>
    exact .ctrRmw k op g x τ e n he h1 h2 h3 h4 h5 fun old hG ho hle hl =>
      ⟨(h6 old hG ho hle hl).1, (h6 old hG ho hle hl).2, hT _ he old⟩
  | alloc s' A x a τ e ta ws k wold old us he h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    exact .alloc s' A x a τ e ta ws k wold old us he h1 h2 h3 h4 h5 h6 h7 h8 fun l ini hl => h9 l ini hl (hT _ he)
  | newStore kr A V s' x a ty e w wold old h0 he h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .newStore kr A V s' x a ty e w wold old h0 he h1 h2 h3 h4 h5 h6 h7 h8 h9 fun l hl =>
      h10 l hl (hT _ he true)
  | emit K' buf n Pw Qw hK' hat hd h0 hb hr hq =>
    have hK2 : ms.K = some K' := hK'
    rw [hK] at hK2
    cases hK2
    have hR : ∀ r', U r (Scc.Sem.A64.abi.ret s r') := fun r' => hs
    exact .emit _ buf n Pw Qw hK hat hd h0 hb (fun j hj c1 hp r' hm hok =>
      ⟨⟨(hr j hj c1 hp r' hm hok).1, hR r'⟩, (hr j hj c1 hp r' hm hok).2⟩) hq
  | fence k s' c' he hr hx => exact .fence k s' c' he hr ⟨hx, hT _ he ()⟩

/-- **A segment keeps `r` unmapped**: a segment under `unXa ms r` (its
allocation landings asked only with `r` unmapped) whose outside moves keep
`r` unmapped (`hKu`) is one under `ms` with `r` unmapped at its entry and
its exits. -/
theorem SegW.keepUn {W : Frag isaLSE2} {K : State → State → Prop} {p : CoreTerm.Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {P Q : Frag isaLSE2} {r : Range}
    (hK : ms.K = some Scc.Sem.A64.abi) (h : SegW W K p lbl (unXa ms r) P Q)
    (hKu : ∀ s c, W s c → ∀ s', K s s' → U r s → U r s') :
    SegW W K p lbl ms (fun s c => P s c ∧ U r s) (fun s c => Q s c ∧ U r s) := by
  obtain ⟨inv, hP, hiW, hcl⟩ := h
  refine ⟨fun s c => inv s c ∧ U r s, fun s c hp => ⟨hP s c hp.1, hp.2⟩, fun s c h => hiW s c h.1,
    fun s c hi => ?_⟩
  obtain ⟨hout, hk⟩ := hcl s c hi.1
  refine ⟨fun hK' => (out_un hK hi.2 (hout hK')).mono ?_, fun s' hks => ?_⟩
  · exact fun s c hx => hx.1.elim (fun h => .inl ⟨h, hx.2⟩) fun h => .inr ⟨h, hx.2⟩
  · obtain ⟨c', hr, hx⟩ := hk s' hks
    have hu := hKu s c (hiW s c hi.1) s' hks hi.2
    exact ⟨c', hr, hx.elim (fun h => .inl ⟨h, hu⟩) fun h => .inr ⟨h, hu⟩⟩

/-- **The take of a range `rS` disjoint from `r` keeps `r` unmapped**
(`unowned_take_keep`; `skip` and `setDmem` keep `WideSt`). -/
theorem take_un {rS r : Range} {s : State} (pm : _root_.Mem 64)
    (hd : r.Disjoint rS) (h1 : r.lo + r.size ≤ 2 ^ 64) (hr : rS.lo + rS.size ≤ 2 ^ 64) (hs : U r s) :
    U r (afterTake s pm rS) :=
  ⟨hs.1, unowned_take_keep hs.2 hd h1 hr pm⟩

/-- info: 'Spike.Lib.A64.KeepUn.SegW.keepUn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.KeepUn.SegW.keepUn

/-- info: 'Spike.Lib.A64.KeepUn.take_un' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.KeepUn.take_un

end Spike.Lib.A64.KeepUn
