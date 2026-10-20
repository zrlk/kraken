import WeakCore.TermPubOnly
import WeakCore.TermPtrKey

/-!
# TermK2a: the owner-step preservation of `(M)+(R)` (K-2a)

`TermPtrRts.PtrRtsThreadGL`'s proof.

1. `tmin` across the step (`tminOf_step`): the promises shrink (`tstep_fulfil`), memory is
   extended (`tstep_appUp`), a surviving promise's cell keeps its `sto` entry (old cells by
   `sto ⊆ sto'`, new ones by `hNF`), and the old `tmin` survives (K-3, `noFul_step_typed`).  So
   `tmin` is the same before and after (a `none` stays `none`).
-/

namespace TermK2a
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermPtrRts TermPtrStab TermOwnG0Defs TermCut
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## 1. `tmin` across the step -/

/-- **`tmin` is unchanged by a non-`publish a` owner step.** -/
theorem tminOf_step {p : Prog} {g : G} {E : TEnv} {sto sto' : Sto} {mem : Memory} {pairs : List Ts}
    {th : TTh} {a : AllocLabel} {r : Memory × List Ts × TTh}
    (hk : g.k.storeDepRts = true) (h1 : ∀ l c, E.sto l = some c → sto l = some c)
    (h3 : ∀ l c, sto l = some c → sto' l = some c)
    (hT : ThInvE p E th) (hm : MemInv g E (stOf mem pairs th))
    (hR : PtrRtsE sto (stOf mem pairs th) th a) (hnp : ¬ PubAt th a)
    (hr : r ∈ tstep g mem pairs th)
    (hNF : ∀ u ∈ r.2.2.promises, ∀ m, r.1[u]? = some m → sto m.loc.label = none → sto' m.loc.label = none) :
    tminOf sto' (stOf r.1 r.2.1 r.2.2) a = tminOf sto (stOf mem pairs th) a := by
  have hlt : ∀ u ∈ th.promises, u < mem.size := hm.2.2.1
  have hsub := (TermFul.tstep_fulfil hlt (MemInv_nopair hm) hr).1
  have hext : ∀ (u : Ts) (m : Msg), mem[u]? = some m → r.1[u]? = some m := (tstep_appUp hr).2.1
  refine tminOf_shrink (fun u hu => hsub.subset hu) (fun u hu => ?_)
    (fun t ht => TermPubOnly.noFul_step_typed p E sto g mem pairs th a t r hk h1 hT hm hR ht hr hnp)
  have hu0 : u < mem.size := hlt u (hsub.subset hu)
  have hm1 : mem[u]? = some mem[u] := Array.getElem?_eq_getElem hu0
  have hm2 := hext u _ hm1
  refine edgeB_agree hm1 hm2 ?_
  cases e : sto mem[u].loc.label with
  | none => exact hNF u hu _ hm2 e
  | some cl => exact h3 _ _ e

/-- `PtrRtsE` after the step reduces to `(M)+(R)` at the old `tmin`. -/
theorem ptrRtsE_step {p : Prog} {g : G} {E : TEnv} {sto sto' : Sto} {mem : Memory} {pairs : List Ts}
    {th : TTh} {a : AllocLabel} {r : Memory × List Ts × TTh}
    (hk : g.k.storeDepRts = true) (h1 : ∀ l c, E.sto l = some c → sto l = some c)
    (h3 : ∀ l c, sto l = some c → sto' l = some c)
    (hT : ThInvE p E th) (hm : MemInv g E (stOf mem pairs th))
    (hR : PtrRtsE sto (stOf mem pairs th) th a) (hnp : ¬ PubAt th a)
    (hr : r ∈ tstep g mem pairs th)
    (hNF : ∀ u ∈ r.2.2.promises, ∀ m, r.1[u]? = some m → sto m.loc.label = none → sto' m.loc.label = none)
    (hMR : ∀ t, tminOf sto (stOf mem pairs th) a = some t →
      MemRts sto' t a r.1 r.2.2.promises ∧ ThRts t a r.2.2) :
    PtrRtsE sto' (stOf r.1 r.2.1 r.2.2) r.2.2 a ∧
      ∀ t, tminOf sto (stOf mem pairs th) a = some t → tminOf sto' (stOf r.1 r.2.1 r.2.2) a = some t := by
  have e := tminOf_step hk h1 h3 hT hm hR hnp hr hNF
  refine ⟨fun t ht => ?_, fun t ht => e.trans ht⟩
  rw [e] at ht
  exact hMR t ht

/-! ## 0. The binding contract (shared with the blocks) -/

/-- Every binding of a thread's frame and stack environments. -/
def Binds (th : TTh) : List (String × Ty × List Word) := th.env ++ th.stack.flatMap (·.env)

/-- If `w` names `a`, a counted word of an old binding names `a` with no larger `rts`. -/
def OldW (a : AllocLabel) (th : TTh) (w : Word) : Prop :=
  Names a w → ∃ b ∈ Binds th, ∃ w0 ∈ pubWords b.2.1 b.2.2, Names a w0 ∧ w0.rts ≤ w.rts

/-- Every label of `w` is named by a counted word of an old binding. -/
def OldL (th : TTh) (w : Word) : Prop :=
  ∀ l, Names l w → ∃ b ∈ Binds th, ∃ w0 ∈ pubWords b.2.1 b.2.2, Names l w0

/-- `w` was loaded from a non-promise message at a counted slot of a cell of `sto` (`MemRtsC`'s
premise), naming no label the message does not, with `rts` at least the message index. -/
def LoadW (sto : Sto) (mem : Memory) (pairs P : List Ts) (w : Word) : Prop :=
  ∃ u m cl, mem[u]? = some m ∧ u ∉ P ∧ sto m.loc.label = some cl ∧ (∀ l, Names l w → Names l (mw m)) ∧
    u ≤ w.rts ∧
    ((NotSnd cl.ty m.loc.offset ∧ CntOK cl.ty m.loc.offset (mw m)) ∨
      ∃ v m0, v + 1 = u ∧ v ∈ pairs ∧ mem[v]? = some m0 ∧ m0.loc.label = m.loc.label ∧
        CntPairOK cl.ty m0.loc.offset (mw m0) (mw m))

/-- A new counted word: for (R), old-covered at `a` or loaded; for `ThLbl`, old labels, loaded, or
labels of the step's set `N` (`publish`'s new frontier). -/
def NewW (sto : Sto) (mem : Memory) (pairs P : List Ts) (a : AllocLabel) (N : AllocLabel → Prop) (th : TTh)
    (w : Word) : Prop :=
  (OldW a th w ∨ LoadW sto mem pairs P w) ∧ (OldL th w ∨ LoadW sto mem pairs P w ∨ ∀ l, Names l w → N l)

/-- A result value of the step is fine: every counted word is new-fine. -/
def ValB (sto : Sto) (s : St) (a : AllocLabel) (N : AllocLabel → Prop) (th : TTh) (rt : Ty) (ws : List Word) :
    Prop :=
  ∀ w ∈ pubWords rt ws, NewW sto s.mem s.pairs th.promises a N th w

/-- **The step's binding contract**: every binding after the step is an old one or fine. -/
def StepB (sto : Sto) (mem : Memory) (pairs : List Ts) (a : AllocLabel) (N : AllocLabel → Prop) (th th' : TTh) :
    Prop :=
  ∀ b ∈ Binds th', b ∈ Binds th ∨ ∀ w ∈ pubWords b.2.1 b.2.2, NewW sto mem pairs th.promises a N th w

theorem mem_binds_env {th : TTh} {b : String × Ty × List Word} (h : b ∈ th.env) : b ∈ Binds th :=
  List.mem_append_left _ h

theorem mem_binds_stack {th : TTh} {b : String × Ty × List Word} {f : Frame} (hf : f ∈ th.stack)
    (h : b ∈ f.env) : b ∈ Binds th :=
  List.mem_append_right _ (List.mem_flatMap.2 ⟨f, hf, h⟩)

/-- A counted word of an old binding is new-fine. -/
theorem newW_of_mem {sto : Sto} {mem : Memory} {pairs P : List Ts} {a : AllocLabel} {N : AllocLabel → Prop}
    {th : TTh} {b : String × Ty × List Word} (hb : b ∈ Binds th) {w : Word}
    (hw : w ∈ pubWords b.2.1 b.2.2) : NewW sto mem pairs P a N th w :=
  ⟨.inl fun hn => ⟨b, hb, w, hw, hn, Nat.le_refl _⟩, .inl fun _ hn => ⟨b, hb, w, hw, hn⟩⟩

/-- A word naming no label is new-fine. -/
theorem newW_of_noName {sto : Sto} {mem : Memory} {pairs P : List Ts} {a : AllocLabel} {N : AllocLabel → Prop}
    {th : TTh} {w : Word} (h : ∀ l, ¬ Names l w) : NewW sto mem pairs P a N th w :=
  ⟨.inl fun hn => absurd hn (h a), .inl fun l hn => absurd hn (h l)⟩

/-- `let_ x op e` (not a call): the post bindings are the old ones and the op's result. -/
theorem stepB_let {sto : Sto} {s : St} {a : AllocLabel} {N : AllocLabel → Prop} {th th' : TTh} {x : String}
    {rt : Ty} {ws : List Word}
    (he : th'.env = (x, rt, ws) :: th.env) (hst : th'.stack = th.stack) (hv : ValB sto s a N th rt ws) :
    StepB sto s.mem s.pairs a N th th' := by
  intro b hb
  unfold Binds at hb
  rw [he, hst] at hb
  rcases List.mem_append.1 hb with hb | hb
  · rcases List.mem_cons.1 hb with e | hb
    · subst e; exact .inr hv
    · exact .inl (mem_binds_env hb)
  · exact .inl (List.mem_append_right _ hb)

/-! ## 2. Assembly: (R) from the contract -/

/-- **(R) after the step**, from (R) before, `MemRtsC` before and the contract. -/
theorem thRts_of_stepB {sto : Sto} {mem : Memory} {pairs : List Ts} {N : AllocLabel → Prop} {th th' : TTh}
    {t : Ts} {a : AllocLabel}
    (hR : ThRts t a th) (hC : MemRtsC sto t a mem pairs th.promises) (hB : StepB sto mem pairs a N th th') :
    ThRts t a th' := by
  have hold : ∀ b ∈ Binds th, ∀ w ∈ pubWords b.2.1 b.2.2, Names a w → t ≤ w.rts := by
    intro b hb w hw hn
    unfold Binds at hb
    rcases List.mem_append.1 hb with hb | hb
    · exact hR.1 _ _ _ hb w hw hn
    · obtain ⟨f, hf, hbf⟩ := List.mem_flatMap.1 hb
      exact hR.2 f hf _ _ _ hbf w hw hn
  have hall : ∀ b ∈ Binds th', ∀ w ∈ pubWords b.2.1 b.2.2, Names a w → t ≤ w.rts := by
    intro b hb w hw hn
    rcases hB b hb with hb0 | hnew
    · exact hold b hb0 w hw hn
    · rcases (hnew w hw).1 with hO | ⟨u, m, cl, hmu, hnp, hcl, hval, hrts, hslot⟩
      · obtain ⟨b0, hb0, w0, hw0, hn0, hle⟩ := hO hn
        exact Nat.le_trans (hold b0 hb0 w0 hw0 hn0) hle
      · have hnm : Names a (mw m) := hval a hn
        exact Nat.le_trans (hC u m cl hmu hnp hcl hnm hslot) hrts
  exact ⟨fun x rt ws hm => hall _ (mem_binds_env hm), fun f hf x rt ws hm => hall _ (mem_binds_stack hf hm)⟩

end TermK2a

#print axioms TermK2a.tminOf_step
#print axioms TermK2a.ptrRtsE_step
#print axioms TermK2a.stepB_let
#print axioms TermK2a.thRts_of_stepB
