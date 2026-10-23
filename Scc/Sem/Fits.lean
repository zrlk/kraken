/-
**Every target value is a 64-bit value** (`Scc/DESIGN.md` §9.0).

A Kraken value (`Val`) is 128 bits wide. The certified fragment only ever
writes a 64-bit register widened to 128 bits (`Fit64Tree`,
`Scc/Cert/Rt/WideA64.lean`, `Scc/Cert/Rt/WideX64.lean`), and the initial
words are the layout's image and the `.rodata` words, all below `2^64`. So
every value a load reads fits in 64 bits, and its low 64 bits, which the
loading register receives, are the whole value (`valRep_setWidth_of_fits`).

- `MemRel.Fits`: every message of a target memory is of a 64-bit value;
  `InitFits`: so is every initial value. `InitFits` is a fact of the loaded
  memory only: no step changes `Memory.init`.
- `fits_empty`, `fits_append`: no message, and one more 64-bit message.
- `initFits_words`, `image_fit`, `rodataWords_fit`: the loaded initial
  words.
- `fits_runTree`, `fits_stepOneWith`, `fits_stepOne`: a run of a tree, or
  an instruction, writing 64-bit values only keeps `Fits`.
- `fits_promise_cert`, `fits_promise_cert_on`: a certified promise step of
  code writing 64-bit values only (on an invariant `P`) keeps `Fits`
  (`certOkC_prom_good_on`).
- `read?_fits`: a read of a `Fits` memory with `InitFits` returns a 64-bit
  value; `valRep_setWidth_of_fits`: then its low 64 bits represent what
  the whole value represents.
-/
import Scc.Sem.Wide
import Scc.Sem.Target
import Scc.Sem.Coh

namespace Scc.Sem

open Kraken Kraken.Promising

namespace MemRel

/-- **Every target message is of a 64-bit value.** -/
def Fits (tm : Memory) : Prop := ∀ k w, tm.get? k = some w → w.val.toNat < 2 ^ 64

end MemRel

/-- **Every initial value of a target memory is a 64-bit value.** -/
def InitFits (tm : Memory) : Prop := ∀ q ∈ tm.init, q.2.toNat < 2 ^ 64

open MemRel

/-! ## The loaded memory -/

/-- A memory with no message fits. -/
theorem fits_empty {tm : Memory} (h : tm.msgs = #[]) : Fits tm := by
  intro k w hk
  unfold Memory.get? at hk
  split at hk
  · cases hk
  · rw [h] at hk; simp at hk

/-- A natural number below `2^64` as a `Val` fits in 64 bits. -/
theorem toNat_ofNat_fit {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 128 n).toNat < 2 ^ 64 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))]
  exact h

/-- **Initial words of 64-bit values fit** (each ISA's `wordsMem`). -/
theorem initFits_words {ws : List (Nat × Nat)} (hws : ∀ p ∈ ws, p.2 < 2 ^ 64) :
    ∀ q ∈ ws.map (fun p => ((⟨BitVec.ofNat 64 p.1, 8⟩ : Loc), BitVec.ofNat 128 p.2)), q.2.toNat < 2 ^ 64 := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  exact toNat_ofNat_fit (hws p hp)

/-- The image of a well-formed layout is of 64-bit values. -/
theorem image_fit {Λ : Layout} (hwf : Λ.WF) : ∀ p ∈ Λ.image, p.2 < 2 ^ 64 :=
  fun p hp => (hwf.image p hp).2.2

/-- The `.rodata` words are 64-bit values. -/
theorem rodataWords_fit (Λ : Layout) (items : List Kraken.DataImage.Item) (code : String → Option Nat) :
    ∀ p ∈ rodataWords Λ items code, p.2 < 2 ^ 64 := by
  intro p hp
  simp only [rodataWords, Kraken.DataImage.words] at hp
  exact (Kraken.DataImage.wordsN_mem _ _ _ p hp).2

/-! ## Steps -/

/-- **One more 64-bit message keeps `Fits`.** -/
theorem fits_append {tm : Memory} (h : Fits tm) {w : Msg} (hw : w.val.toNat < 2 ^ 64) :
    Fits (tm.append w).1 := by
  intro k w' hk
  by_cases hne : k = tm.last + 1
  · subst hne
    rw [Memory.get?_append_new] at hk
    cases hk; exact hw
  · exact h k w' (CohCoversP.get?_append_ne hk hne)

/-- Appending keeps the initial values. -/
theorem initFits_append {tm : Memory} (h : InitFits tm) (w : Msg) : InitFits (tm.append w).1 := h

section Rules

variable (A : Arch) (tid : Nat)

theorem fits_write {xr : View} {c c' : Ctx} {iv' : InstrViews} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} (hv : Fit64 l v)
    (h : c' ∈ writeSuccs A tid iv' c k xcl l v tr extra xr) (hf : Fits c.mem) : Fits c'.mem := by
  rcases (Lower.mem_writeSuccs_iff A tid iv').mp h with ⟨t, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · exact hf
  · exact fits_append hf (w := { loc := l, val := v, tid }) hv

theorem fits_read {iv : InstrViews} {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) (hf : Fits c.mem) : Fits x.2.2.mem := by
  obtain ⟨-, -, -, he⟩ := readSuccs_shape A iv hx
  rw [he]; exact hf

theorem fits_fenceOpt {c : Ctx} (b : Bool) (hf : Fits c.mem) : Fits (if b then fenceStep c .sy else c).mem := by
  cases b
  · exact hf
  · show Fits (fenceStep c .sy).mem; rw [fenceStep_mem]; exact hf

theorem fits_rmwPost {c : Ctx} (k : RmwKind) (noRet : Bool) (l : Loc) (hf : Fits c.mem) :
    Fits (rmwPost A k noRet l c).mem := by
  have : (rmwPost A k noRet l c).mem = c.mem := by unfold rmwPost; split <;> rfl
  rw [this]; exact hf

/-- **A run of a tree writing 64-bit values only keeps `Fits`.** -/
theorem fits_runTree (iv : InstrViews) {σ : Type} (tree : EvTree σ) (hW : Fit64Tree tree) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → Fits c.mem → Fits c'.mem := by
  induction tree with
  | done s =>
    intro c s' c' h hf
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hf
  | fault m => intro c s c' h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' h hf
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i (hW i) c s c' h hf
  | load k xcl l ret ih =>
    intro c s c' h hf
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    exact ih x.2.1 (hW x.2.1) x.2.2 s c' h (fits_read A hx hf)
  | store k xcl l v ret ih =>
    intro c s c' h hf
    obtain ⟨hl, hW⟩ := hW
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact ih true (hW true) c0 s c' h (fits_write A tid hl hc0 hf)
    · rw [List.mem_ite_nil_right] at h
      exact ih false (hW false) _ s c' h.2 hf
  | fence k ret ih =>
    intro c s c' h hf
    simp only [runTree] at h
    exact ih () (hW ()) _ s c' h (by rw [fenceStep_mem]; exact hf)
  | rmw k noRet l op ret ih =>
    intro c s c' h hf
    obtain ⟨hl, hW⟩ := hW
    simp only [runTree] at h
    have h1 := fits_fenceOpt A.rmwFence hf
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := fits_read A h2 h1
    simp only at h
    split at h
    · exact ih old (hW old) _ s c' h (fits_fenceOpt A.rmwFence h12)
    · rename_i new hnew
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      exact ih old (hW old) _ s c' h
        (fits_fenceOpt A.rmwFence (fits_rmwPost A k noRet l (fits_write A tid (hl old new hnew) hc3 h12)))

end Rules

/-- **One instruction under `cexec` writing 64-bit values only keeps
`Fits`.** -/
theorem fits_stepOneWith {I : ISA} (A : Arch) {cs : CertSem I} {t : Thread I}
    (hW : ∀ tree, cs.exec t.st = some tree → Fit64Tree tree) {tid : Nat} {mem : Memory}
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : cs.step A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hf : Fits mem) : Fits o.mem := by
  unfold CertSem.step stepOneWithD at hstep
  cases hex : cs.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok q =>
      obtain ⟨st, c'⟩ := q
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, -, rfl⟩ := ho
      exact fits_runTree A tid _ tree (hW _ hex) _ st c' hr hf

/-- **One instruction step (`stepOne`, the ISA's `exec`) writing 64-bit
values only keeps `Fits`.** -/
theorem fits_stepOne {I : ISA} (A : Arch) {t : Thread I} (hW : ∀ tree, I.exec t.st = some tree → Fit64Tree tree)
    {tid : Nat} {mem : Memory} {outs : List (Except String (Kraken.Promising.Outcome I))}
    (hstep : stepOne A t tid mem = some outs) {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    (hf : Fits mem) : Fits o.mem :=
  fits_stepOneWith A (cs := CertSem.ofExec I.exec) hW hstep ho hf

/-- **A certified promise step keeps `Fits`**, for code writing 64-bit
values only from the states of an invariant `P` it keeps, from a thread at
a `P` state: the promised message is of a 64-bit value. -/
theorem fits_promise_cert_on {I : ISA} {A : Arch} {cs : CertSem I}
    {P : I.State → Prop} (hW : Fit64CodeOn P cs.exec) (hP : WideInv P cs.exec) {t : Thread I} (hst : P t.st)
    {tid : Nat} {tm : Memory} {w : Msg}
    (hc : CertOkC A cs tid (Live.Sem.promThread t tm w) (tm.append w).1) (hf : Fits tm) :
    Fits (tm.append w).1 :=
  fits_append hf (certOkC_prom_good_on hW hP (t := Live.Sem.promThread t tm w) hst hc
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) Memory.get?_append_new)

/-- **A certified promise step of code writing 64-bit values only keeps
`Fits`.** -/
theorem fits_promise_cert {I : ISA} {A : Arch} {cs : CertSem I}
    (hW : Fit64Code cs.exec) {t : Thread I} {tid : Nat} {tm : Memory} {w : Msg}
    (hc : CertOkC A cs tid (Live.Sem.promThread t tm w) (tm.append w).1) (hf : Fits tm) :
    Fits (tm.append w).1 :=
  fits_append hf (certOkC_prom_good hW hc (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    Memory.get?_append_new)

/-! ## Reads -/

/-- **A read of a fitting memory returns a 64-bit value**: a message's, or
an initial value (as declared, else `0`). -/
theorem read?_fits {tm : Memory} (hf : Fits tm) (hi : InitFits tm) {l : Loc} {k : Time} {v : Val}
    (h : tm.read? l k = some v) : v.toNat < 2 ^ 64 := by
  unfold Memory.read? at h
  split at h
  · cases h
    unfold Memory.initVal
    cases hq : tm.init.find? (·.1 == l) with
    | none => simp
    | some q => exact hi q (List.mem_of_find?_eq_some hq)
  · split at h
    · rename_i w hw
      split at h
      · cases h; exact hf _ _ hw
      · cases h
    · cases h

/-- **The low 64 bits of a 64-bit value represent what the value does**
(`ValRep`): the register a load writes receives the whole value read. -/
theorem valRep_setWidth_of_fits {lbl : WeakMem.AllocLabel → Option Nat} {val : WeakMem.Val} {v : Val}
    (h : ValRep lbl val v.toNat) (hv : v.toNat < 2 ^ 64) : ValRep lbl val (v.setWidth 64).toNat := by
  rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hv]

/-! ## Tests -/

/-- A 128-bit value above `2^64` does not fit, so its low 64 bits lose
information: `valRep_setWidth_of_fits` needs `hv`. -/
example : ¬ (((BitVec.ofNat 128 (2 ^ 64 + 5)).setWidth 64).toNat = (BitVec.ofNat 128 (2 ^ 64 + 5)).toNat) := by
  decide

/-- A store of a value above `2^64` is not `Fit64`. -/
example : ¬ Fit64 ⟨0, 8⟩ (BitVec.ofNat 128 (2 ^ 64)) := by
  unfold Fit64; decide

end Scc.Sem
