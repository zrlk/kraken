/-
**The segment judgement's rows along a map of target states**
(ISA-neutral; for moving the consumer obligations from one executable to
another with the same machine states, e.g. a text and the same text with a
tail appended). A row of `s` (`Out`, `OutS`) is a row of `r s` landing in the
image of its landing, when the step of `r s` is the step of `s` with every
leaf mapped and the memory sides correspond along `r` at `s`.

- `img`, `imgS`: the image of a fragment along a state map;
- `Leaves`, `LeafQ`, `MemSide.withQ`, `out_leaf`: a row's landings, and its
  allocation fragments, may carry any property every leaf of the state's
  step has;
- `silentTree_map`: a silent tree's image;
- `MsMap`, `MsMap.sysOk`, `out_map`: a row along a state map;
- `outS_map`, `pend_map`, `outS_leaf`: the same at any depth, for a pending
  landing, and with leaf properties;
- `runTree_map`: running a mapped tree.
-/
import Spike.Lib.SegS

namespace Spike.Lib.RestTail

open CoreLang CoreTerm
open Kraken.Promising
open Kraken.Promising.Lower (SilentTree)
open Spike.Lib

/-- The image of a fragment along a state map. -/
def img {I : ISA} (r : I.State → I.State) (X : Frag I) : Frag I := fun s' c => ∃ s, X s c ∧ s' = r s

theorem img_of {I : ISA} {r : I.State → I.State} {X : Frag I} {s : I.State} {c : Ctl} (h : X s c) :
    img r X (r s) c := ⟨s, h, rfl⟩

/-- A silent tree's image is silent, onto the image of its leaves. -/
theorem silentTree_map {σ : Type} (r : σ → σ) {P : σ → Prop} :
    ∀ {t : EvTree σ}, SilentTree P t → SilentTree (fun s' => ∃ s, P s ∧ s' = r s) (EvTree.map r t)
  | .done _, h => ⟨_, h, rfl⟩
  | .choose _ _, h => ⟨h.1, fun i => silentTree_map r (h.2 i)⟩
  | .fault _, h => h.elim
  | .load .., h => h.elim
  | .store .., h => h.elim
  | .rmw .., h => h.elim
  | .fence .., h => h.elim

/-- **The memory sides along a state map** at the state `s`: the same
state-free fields; the state fields of `ms'` at `r s` as those of `ms` at
`s` (allocation fragments along `r`); the kernel model the same, commuting
with `r` at `s`. -/
structure MsMap {I : ISA} (r : I.State → I.State) (ms ms' : MemSide I) (s : I.State) : Prop where
  rd : ms'.rd = ms.rd
  rt : ms'.rt = ms.rt
  K : ms'.K = ms.K
  G : ms'.G = ms.G
  heap : ms'.heap = ms.heap
  ctr : ms'.ctr = ms.ctr
  units : ms'.units = ms.units
  off : ms'.off = ms.off
  cells : ms'.cells = ms.cells
  mp : ms'.mp = ms.mp
  lo : ms'.lo = ms.lo
  pub : ms'.pub = ms.pub
  newOk : ms'.newOk = ms.newOk
  own : ms'.own (r s) = ms.own s
  abortAt : ms'.abortAt (r s) ↔ ms.abortAt s
  pl : ∀ c, ms.pl s c → ms'.pl (r s) c
  xa : ∀ l b n s' c, ms.xa l b n s' c → ms'.xa l b n (r s') c
  bo : ∀ b c P, ms.bo s b c P → ms'.bo (r s) b c P
  we : ∀ c, ms.we s c → ms'.we (r s) c
  kAt : ∀ K, ms.K = some K → K.atSys (r s) = K.atSys s ∧ K.nr (r s) = K.nr s ∧ K.arg (r s) = K.arg s ∧
    (∀ x, K.ret (r s) x = r (K.ret s x)) ∧
    (∀ call, Scc.Sem.Kernel.certSuccs K (r s) call = (Scc.Sem.Kernel.certSuccs K s call).map r)

theorem MsMap.sysOk {I : ISA} {r : I.State → I.State} {ms ms' : MemSide I} {s : I.State} {p : Prog} {c : Ctl}
    {call : Scc.Sem.Kernel.Call} (hm : MsMap r ms ms' s) (h : SysOk p ms s c call) :
    SysOk p ms' (r s) c call := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun v hv ha => ?_⟩
  obtain ⟨c', hr, hp, hx⟩ := h4 v hv (fun ha' => ha (hm.abortAt.2 ha'))
  exact ⟨c', hr, hm.pl _ hp, hx⟩

/-- Every leaf of a tree has the property `Q`. -/
def Leaves {σ : Type} (Q : σ → Prop) : EvTree σ → Prop
  | .done s => Q s
  | .fault _ => True
  | .choose _ k => ∀ i, Leaves Q (k i)
  | .load _ _ _ ret => ∀ v, Leaves Q (ret v)
  | .store _ _ _ _ ret => ∀ b, Leaves Q (ret b)
  | .rmw _ _ _ _ ret => ∀ v, Leaves Q (ret v)
  | .fence _ ret => ∀ u, Leaves Q (ret u)

/-- **Every state a row of `s` may land in has `Q`**: every leaf of the
step of `s`, and every state the kernel model may resume `s` in. -/
structure LeafQ {I : ISA} (Q : I.State → Prop) (ms : MemSide I) (s : I.State) : Prop where
  exec : ∀ t, I.exec s = some t → Leaves Q t
  ret : ∀ K, ms.K = some K → ∀ x, Q (K.ret s x)
  succs : ∀ K, ms.K = some K → ∀ call, ∀ s' ∈ Scc.Sem.Kernel.certSuccs K s call, Q s'

/-- The memory side whose allocation fragments also ask `Q`. -/
def _root_.Spike.Lib.MemSide.withQ {I : ISA} (ms : MemSide I) (Q : I.State → Prop) : MemSide I :=
  { ms with xa := fun l b n s c => ms.xa l b n s c ∧ Q s }

theorem silentTree_and {σ : Type} {P Q : σ → Prop} :
    ∀ {t : EvTree σ}, SilentTree P t → Leaves Q t → SilentTree (fun s => P s ∧ Q s) t
  | .done _, h, hq => ⟨h, hq⟩
  | .choose _ _, h, hq => ⟨h.1, fun i => silentTree_and (h.2 i) (hq i)⟩
  | .fault _, h, _ => h.elim
  | .load .., h, _ => h.elim
  | .store .., h, _ => h.elim
  | .rmw .., h, _ => h.elim
  | .fence .., h, _ => h.elim

/-- **A row's landings carry every property of its leaves** (`LeafQ`), its
allocation fragments too (`MemSide.withQ`). -/
theorem out_leaf {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I} {X : Frag I}
    {s : I.State} {c : Ctl} {Q : I.State → Prop} (hq : LeafQ Q ms s) (h : Out p lbl ms X s c) :
    Out p lbl (ms.withQ Q) (fun s c => X s c ∧ Q s) s c := by
  cases h with
  | silent s' c' he hr hx => exact .silent s' c' he hr ⟨hx, hq.exec _ he⟩
  | choice P t he hs hP =>
    exact .choice _ t he (silentTree_and hs (hq.exec _ he))
      fun s' ⟨hp, hq'⟩ => let ⟨c', hr, hx⟩ := hP s' hp; ⟨c', hr, hx, hq'⟩
  | load kl A g x a e ty w he ht hv hA hX hl =>
    exact .load kl A g x a e ty w he ht hv hA (fun v w' hr hw => ⟨hX v w' hr hw, hq.exec _ he v⟩) hl
  | store kr A V s' x a b e ty tb w wb he ht hv hA hb hV hX hl =>
    exact .store kr A V s' x a b e ty tb w wb he ht hv hA hb hV ⟨hX, hq.exec _ he true⟩ hl
  | rtStore kr L V s' c' he hrt hmp hG hr hX =>
    exact .rtStore kr L V s' c' he hrt hmp hG hr ⟨hX, hq.exec _ he true⟩
  | rtLoad kl L g c' he hrt hmp hr hX =>
    exact .rtLoad kl L g c' he hrt hmp hr fun v hG ho => ⟨hX v hG ho, hq.exec _ he v⟩
  | rtRmw k L op g c' he hrt hmp hr hX =>
    exact .rtRmw k L op g c' he hrt hmp hr fun old hG ho =>
      ⟨(hX old hG ho).1, (hX old hG ho).2, hq.exec _ he old⟩
  | sys K call hK hs hd hok hX =>
    exact .sys K call hK hs hd hok fun s' hs' =>
      let ⟨c', hr, hx⟩ := hX s' hs'; ⟨c', hr, hx, hq.succs K hK call s' hs'⟩
  | holdLoad kl A g x sa u v e he hxs hA hh hX =>
    exact .holdLoad kl A g x sa u v e he hxs hA hh fun v' w' hr hw => ⟨hX v' w' hr hw, hq.exec _ he v'⟩
  | xchgStore kr A V s' x sa u v e tv wv wold he hxs hA hh hv hV hX =>
    exact .xchgStore kr A V s' x sa u v e tv wv wold he hxs hA hh hv hV ⟨hX, hq.exec _ he true⟩
  | ctrRmw k op g x τ e n he hrt hmp hs hh hop hX =>
    exact .ctrRmw k op g x τ e n he hrt hmp hs hh hop fun old hG ho hc hlo =>
      ⟨(hX old hG ho hc hlo).1, (hX old hG ho hc hlo).2, hq.exec _ he old⟩
  | alloc s' A x a τ e ta ws k wold old us he ht hv hk hh hold hA hu haccs hX =>
    exact .alloc s' A x a τ e ta ws k wold old us he ht hv hk hh hold hA hu haccs
      fun l ini hl => ⟨hX l ini hl, hq.exec _ he⟩
  | newStore kr A V s' x a t e w wold old hn he hmp hT hv hacc hV hh hold hA hu hX =>
    exact .newStore kr A V s' x a t e w wold old hn he hmp hT hv hacc hV hh hold hA hu
      fun l hl => ⟨hX l hl, hq.exec _ he true⟩
  | emit K buf n Pw Qw hK hs hd hrun hbo hX hQ =>
    exact .emit K buf n Pw Qw hK hs hd hrun hbo
      (fun j hj c1 hp x hx hw => ⟨⟨(hX j hj c1 hp x hx hw).1, hq.ret K hK x⟩, (hX j hj c1 hp x hx hw).2⟩) hQ
  | fence k s' c' he hf hX => exact .fence k s' c' he hf ⟨hX, hq.exec _ he ()⟩

/-- **A row along a state map**: where the step of `r s` is the step of `s`
with every landing mapped (`hex`) and the memory sides correspond at `s`
(`hm`), a row of `s` under `ms` landing in `X` is one of `r s` under `ms'`
landing in `X`'s image. -/
theorem out_map {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms ms' : MemSide I} {X : Frag I}
    {s : I.State} {c : Ctl} (r : I.State → I.State)
    (hex : I.exec (r s) = (I.exec s).map (EvTree.map r)) (hm : MsMap r ms ms' s)
    (h : Out p lbl ms X s c) : Out p lbl ms' (img r X) (r s) c := by
  cases h with
  | silent s' c' he hr hx => exact .silent (r s') c' (by rw [hex, he]; rfl) hr (img_of hx)
  | choice P t he hs hP =>
    refine .choice _ (EvTree.map r t) (by rw [hex, he]; rfl) (silentTree_map r hs) ?_
    rintro _ ⟨s', hp, rfl⟩
    obtain ⟨c', hr, hx⟩ := hP s' hp
    exact ⟨c', hr, img_of hx⟩
  | load kl A g x a e ty w he ht hv hA hX hl =>
    exact .load kl A (r ∘ g) x a e ty w (by rw [hex, he]; rfl) ht hv hA
      (fun v w' hr hw => img_of (hX v w' (hm.rd ▸ hr) hw)) hl
  | store kr A V s' x a b e ty tb w wb he ht hv hA hb hV hX hl =>
    exact .store kr A V (r s') x a b e ty tb w wb (by rw [hex, he]; rfl) ht hv hA hb hV (img_of hX) hl
  | rtStore kr L V s' c' he hrt hmp hG hr hX =>
    exact .rtStore kr L V (r s') c' (by rw [hex, he]; rfl) (hm.rt ▸ hrt) (hm.mp ▸ hmp) (hm.G ▸ hG) hr
      (img_of hX)
  | rtLoad kl L g c' he hrt hmp hr hX =>
    exact .rtLoad kl L (r ∘ g) c' (by rw [hex, he]; rfl) (hm.rt ▸ hrt) (hm.mp ▸ hmp) hr
      (fun v hG ho => img_of (hX v (hm.G ▸ hG) (fun w hw => ho w (hm.own ▸ hw))))
  | rtRmw k L op g c' he hrt hmp hr hX =>
    exact .rtRmw k L op (r ∘ g) c' (by rw [hex, he]; rfl) (hm.rt ▸ hrt) (hm.mp ▸ hmp) hr
      (fun old hG ho =>
        have h := hX old (hm.G ▸ hG) (fun w hw => ho w (hm.own ▸ hw))
        ⟨fun n hn => hm.G ▸ h.1 n hn, img_of h.2⟩)
  | sys K call hK hs hd hok hX =>
    obtain ⟨ha, hn, harg, -, hcs⟩ := hm.kAt K hK
    refine .sys K call (hm.K ▸ hK) (ha ▸ hs) (by rw [hn, harg]; exact hd) (hm.sysOk hok) ?_
    intro s'' hs''
    rw [hcs] at hs''
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs''
    obtain ⟨c', hr, hx⟩ := hX s' hs'
    exact ⟨c', hr, img_of hx⟩
  | holdLoad kl A g x sa u v e he hxs hA hh hX =>
    exact .holdLoad kl A (r ∘ g) x sa u v e (by rw [hex, he]; rfl) hxs hA hh
      (fun v' w' hr hw => img_of (hX v' w' (hm.rd ▸ hr) hw))
  | xchgStore kr A V s' x sa u v e tv wv wold he hxs hA hh hv hV hX =>
    exact .xchgStore kr A V (r s') x sa u v e tv wv wold (by rw [hex, he]; rfl) hxs hA hh hv hV (img_of hX)
  | ctrRmw k op g x τ e n he hrt hmp hs hh hop hX =>
    refine .ctrRmw k op (r ∘ g) x τ e n (by rw [hex, he, hm.ctr]; rfl) (by rw [hm.ctr, hm.rt]; exact hrt)
      (by rw [hm.ctr, hm.mp]; exact hmp) (hm.newOk ▸ hs) hh (by rw [hm.units]; exact hop) ?_
    intro old hG ho hc hlo
    rw [hm.ctr, hm.G, hm.units] at *
    rw [hm.cells] at hc
    rw [hm.lo] at hlo
    have h := hX old hG (fun w hw => ho w (by rw [hm.own]; exact hw)) hc hlo
    exact ⟨h.1, img_of h.2⟩
  | alloc s' A x a τ e ta ws k wold old us he ht hv hk hh hold hA hu haccs hX =>
    refine .alloc (r s') A x a τ e ta ws k wold old us (by rw [hex, he]; rfl) ht hv hk (hm.ctr ▸ hh) hold
      (by rw [hm.heap, hm.off]; exact hA) (by rw [hm.units, hm.cells]; exact hu) haccs ?_
    intro l ini hl
    exact hm.xa _ _ _ _ _ (hX l ini hl)
  | newStore kr A V s' x a t e w wold old hn he hmp hT hv hacc hV hh hold hA hu hX =>
    refine .newStore kr A V (r s') x a t e w wold old (hm.newOk ▸ hn) (by rw [hex, he]; rfl) (hm.mp ▸ hmp)
      hT hv hacc hV (hm.ctr ▸ hh) hold (by rw [hm.heap, hm.off]; exact hA) (by rw [hm.units, hm.cells]; exact hu) ?_
    intro l hl
    exact hm.xa _ _ _ _ _ (hX l hl)
  | emit K buf n Pw Qw hK hs hd hrun hbo hX hQ =>
    obtain ⟨ha, hn, harg, hret, -⟩ := hm.kAt K hK
    refine .emit K buf n Pw Qw (hm.K ▸ hK) (ha ▸ hs) (by rw [hn, harg]; exact hd) hrun
      (fun j hj c1 hp => hm.bo _ _ _ (hbo j hj c1 hp)) ?_ (fun c1 hq => hm.we _ (hQ c1 hq))
    intro j hj c1 hp x hx hw
    have h := hX j hj c1 hp x hx hw
    exact ⟨hret x ▸ img_of h.1, h.2⟩
  | fence k s' c' he hf hX =>
    exact .fence k (r s') c' (by rw [hex, he]; rfl) (hm.pub ▸ hf) (img_of hX)

/-- The image of a fragment at any depth along a state map. -/
def imgS {I : ISA} (r : I.State → I.State) (X : FragS I) : FragS I := fun s' c fs => ∃ s, X s c fs ∧ s' = r s

/-- **A row at any depth along a state map** (`out_map` at the frames the
source runs to, or the frame step's landing mapped). -/
theorem outS_map {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms ms' : List TermRun.Frame → MemSide I} {X : FragS I} {s : I.State} {c : Ctl} {fs : List TermRun.Frame}
    (r : I.State → I.State) (hex : I.exec (r s) = (I.exec s).map (EvTree.map r))
    (hm : ∀ fs, MsMap r (ms fs) (ms' fs) s) (h : OutS p lbl ms X s c fs) :
    OutS p lbl ms' (imgS r X) (r s) c fs := by
  cases h with
  | pre c₁ fs₁ hr ho =>
    exact .pre c₁ fs₁ hr ((out_map r hex (hm fs₁) ho).mono fun _ _ ⟨s0, hx, he⟩ => ⟨s0, hx, he⟩)
  | frame s' c' fs' he hr hx => exact .frame (r s') c' fs' (by rw [hex, he]; rfl) hr ⟨s', hx, rfl⟩

/-- A pending frame run's landing along a state map. -/
theorem pend_map {I : ISA} {p : Prog} {P : FragS I} {s : I.State} {c : Ctl} {fs : List TermRun.Frame}
    (r : I.State → I.State) (h : Pend p P s c fs) : Pend p (imgS r P) (r s) c fs :=
  let ⟨c', fs', hr, hp⟩ := h
  ⟨c', fs', hr, s, hp, rfl⟩

/-- **A row at any depth carries every property of its leaves** (`out_leaf`
at the frames the source runs to, or the frame step's leaf). -/
theorem outS_leaf {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide I} {X : FragS I} {s : I.State} {c : Ctl} {fs : List TermRun.Frame}
    {Q : I.State → Prop} (hq : ∀ fs, LeafQ Q (ms fs) s) (h : OutS p lbl ms X s c fs) :
    OutS p lbl (fun fs => (ms fs).withQ Q) (fun s c fs => X s c fs ∧ Q s) s c fs := by
  cases h with
  | pre c₁ fs₁ hr h => exact .pre c₁ fs₁ hr (out_leaf (hq fs₁) h)
  | frame s' c' fs' he hr hx => exact .frame s' c' fs' he hr ⟨hx, (hq fs').exec _ he⟩

/-! ### Rows execute or stop at a system call -/

/-- **A row executes or is at a system call** (ISA-neutral): every `Out`
constructor asks `I.exec s = some _`, but `sys` and `emit`, which ask the
memory side's ABI at a system call. -/
theorem Out.exec_or_sys {I : ISA} {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide I} {X : Frag I} {s : I.State} {c : Ctl}
    (h : Out p lbl ms X s c) :
    (I.exec s).isSome ∨ ∃ K, ms.K = some K ∧ K.atSys s = true := by
  cases h <;> first
    | (left; rename_i he; simp [he]; done)
    | (left; simp_all; done)
    | (right; exact ⟨_, ‹_›, ‹_›⟩)
    | skip

/-- `OutS` likewise, at the frames the row is taken at. -/
theorem OutS.exec_or_sys {I : ISA} {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide I} {X : FragS I} {s : I.State} {c : Ctl}
    {fs : List TermRun.Frame} (h : OutS p lbl ms X s c fs) :
    (I.exec s).isSome ∨ ∃ fs₁ K, (ms fs₁).K = some K ∧ K.atSys s = true := by
  cases h with
  | pre c₁ fs₁ _ h =>
    rcases Out.exec_or_sys h with h | ⟨K, hK, hs⟩
    · exact .inl h
    · exact .inr ⟨fs₁, K, hK, hs⟩
  | frame s' c' fs' he _ _ => exact .inl (by simp [he])

/-- **A row's instruction does not fault**, off a system call: every `Out`
constructor but `sys` and `emit` names the instruction's tree, and none of
those is a fault. -/
theorem Out.exec_ne_fault {I : ISA} {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide I} {X : Frag I} {s : I.State} {c : Ctl}
    (h : Out p lbl ms X s c) (m : String) :
    I.exec s ≠ some (.fault m) ∨ ∃ K, ms.K = some K ∧ K.atSys s = true := by
  cases h <;> first
    | (right; exact ⟨_, ‹_›, ‹_›⟩)
    | (left; rename_i ht hs _; rw [ht]; intro he; cases he; exact hs)
    | (left; rename_i he; rw [he]; nofun)
    | (left; intro hf; simp_all)

/-- `OutS` likewise, at the frames the row is taken at. -/
theorem OutS.exec_ne_fault {I : ISA} {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide I} {X : FragS I} {s : I.State} {c : Ctl}
    {fs : List TermRun.Frame} (h : OutS p lbl ms X s c fs) (m : String) :
    I.exec s ≠ some (.fault m) ∨ ∃ fs₁ K, (ms fs₁).K = some K ∧ K.atSys s = true := by
  cases h with
  | pre c₁ fs₁ _ h =>
    rcases Out.exec_ne_fault h m with h | ⟨K, hK, hs⟩
    · exact .inl h
    · exact .inr ⟨fs₁, K, hK, hs⟩
  | frame s' c' fs' he _ _ => exact .inl (by rw [he]; nofun)

section Run

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **Running a mapped tree** gives the runs of the tree with every final
state mapped. -/
theorem runTree_map {σ τ : Type} (r : σ → τ) :
    ∀ (c : Kraken.Promising.Ctx) (t : EvTree σ), runTree A tid iv c (EvTree.map r t) =
      (runTree A tid iv c t).map (Except.map fun x => (r x.1, x.2))
  | _, .done _ => rfl
  | _, .fault _ => rfl
  | c, .choose n k => by
    simp only [EvTree.map, runTree, List.map_flatMap]
    congr 1; funext i; exact runTree_map r c (k i)
  | c, .load k xcl l ret => by
    simp only [EvTree.map, runTree, List.map_flatMap]
    congr 1; funext x; exact runTree_map r _ (ret _)
  | c, .store k xcl l v ret => by
    simp only [EvTree.map, runTree, List.map_append]
    congr 1
    · rw [apply_ite (List.map _), List.map_nil, List.map_flatMap]
      congr 1; congr 1; funext x; exact runTree_map r _ (ret true)
    · split
      · exact runTree_map r _ (ret false)
      · rfl
  | c, .fence k ret => by simp only [EvTree.map, runTree]; exact runTree_map r _ (ret ())
  | c, .rmw k noRet l op ret => by
    simp only [EvTree.map, runTree, List.map_flatMap]
    congr 1; funext x
    split
    · exact runTree_map r _ (ret _)
    · simp only [List.map_flatMap]
      congr 1; funext y; exact runTree_map r _ (ret _)

end Run

end Spike.Lib.RestTail

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.RestTail.out_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.RestTail.out_map

/-- info: 'Spike.Lib.RestTail.out_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.RestTail.out_leaf

/-- info: 'Spike.Lib.RestTail.outS_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.RestTail.outS_map

/-- info: 'Spike.Lib.RestTail.runTree_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.RestTail.runTree_map

/-- info: 'Spike.Lib.RestTail.OutS.exec_or_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.RestTail.OutS.exec_or_sys

/-- info: 'Spike.Lib.RestTail.OutS.exec_ne_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.RestTail.OutS.exec_ne_fault

/-- info: 'Spike.Lib.RestTail.outS_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.RestTail.outS_leaf
