/-
**The abort clause of the x86-64 arena consumer with the `clone` phase, and
the held-range (`H`) load and components**: the parts of
`Spike/Lib/A64ConsumerACorrect.lean`'s `clone`-phase and held-range forms
that do not need `NodesA`'s `Cl` parameter, which
`Spike/Lib/X64ConsumerACorrect.lean` lacks (consumer upgrade).
Same names, same namespaces as AArch64's (`X64ConsumerA`;
`AbortPathS.toC` in `X64ConsumerS`).

- `AbortPathSC`, `AbortPathS.toC`: the abort path with the `threads` abort
  in a phase `Ac` entered only at a state `Cl` marks; the heap disjunct at
  either allocation (`HeapAbortOblA`).
- `TIC`: `TI` with the `clone` phase.
- `pre_loadAH`: the start at any source start `s₀`, over a held predicate.
- `fresh_ofH`: the site's range fresh at the take, off every held range.
- `WriteNoPromAH`, `r_componentsAH`, `r_memInAH`: over `HeldPathS`.

The `Cl` lemmas (`pre_progressAC`/`ACH`, `ti_step_ofAC`/`ACH`, `ti_stepAC`,
`ti_runAC`, `r_abortAC`, …) wait for `NodesA`'s `Cl` parameter.
-/
import Spike.Lib.X64ConsumerACorrect
import Spike.Lib.X64ConsumerAH
import Spike.Lib.HeapAbortBox

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {E : Entry}

/-- **The abort path with a `clone` refusal** (`AbortPathS` with the
`threads` abort): a pair at a resolved abort site may also be at the
`threads` site in the phase `Ac` (after a refused `clone`, `TIC`); `Ac` is
entered only at a state `Cl` marks (`sysC`: off `Cl`, a system call does not
enter it), not by an instruction (`instrC`) or the take (`takeC`). -/
structure AbortPathSC (μ : Marks) (I : InvS) (Cl Ab Ac : State → Prop) (cells ctr : Nat) : Prop where
  at_ : ∀ lbl lsize s c fs, I lbl lsize s c fs → ∀ k a, μ.abortAt k = some a → pcOf s = a →
    ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
      (k = .heap ∧ HeapAbortOblA cells ctr c) ∨ (k = .threads ∧ Ac s)) ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus
  instr : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ab s → abi.atSys s = false → ∀ tree,
    isa.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ab s')
  sys : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ab s → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, Ab s' →
      ∃ fd buf n, call = .write fd buf n ∧ ∀ r, abi.ret s r = s' → Refusal n r
  take : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ab s → ∀ a, μ.site .take = some a → pcOf s = a →
    ∀ m, ¬ Ab (abi.skip (abi.setDmem s m))
  instrC : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ac s → abi.atSys s = false → ∀ tree,
    isa.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ac s')
  sysC : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ac s → abi.atSys s = true → ¬ Cl s → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, ¬ Ac s'
  takeC : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ac s → ∀ a, μ.site .take = some a → pcOf s = a →
    ∀ m, ¬ Ac (abi.skip (abi.setDmem s m))

/-- `AbortPathS` is `AbortPathSC` with no `threads` phase. -/
theorem _root_.Spike.Lib.X64ConsumerS.AbortPathS.toC {Cl Ab : State → Prop} {cells ctr : Nat}
    (h : AbortPathS μ I Ab cells ctr) :
    AbortPathSC μ I Cl Ab (fun _ => False) cells ctr where
  at_ lbl lsize s c fs hI k a ha hpc := by
    obtain ⟨h1, h2⟩ := h.at_ lbl lsize s c fs hI k a ha hpc
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 | h1
    · exact .inl h1
    · exact .inr (.inl h1)
    · exact .inr (.inr (.inl ⟨h1.1, HeapAbortObl.toA h1.2⟩))
  instr := h.instr
  sys := h.sys
  take := h.take
  instrC _ _ _ _ _ _ _ _ tree _ := (allInv_true tree).mono fun _ _ h => h
  sysC _ _ _ _ _ _ _ _ _ _ _ _ _ h := h
  takeC _ _ _ _ _ _ _ _ _ _ _ h := h

/-- **`TI` with the `clone` phase**: `TI` for the `writeErr` phase `Ab`,
and thread 0 in the `threads` phase `Ac` only after a refused `clone`. -/
def TIC (Ab Ac : State → Prop) (tr : List Ev) (t : T.M.Cfg) : Prop :=
  TI Ab tr t ∧ ∀ th, t.1.threads[0]? = some th → Ac th.st → Ev.cloneErr ∈ tr

/-! ## Over a held predicate (`HeldPathS`) -/

open Scc.Cert.Link in
/-- **The start is related at any source start, over a held predicate**
(`pre_loadA` with the source start `s₀` a parameter, one thread `th₀` at
the start pair `⟨th₀.term, th₀.env, none⟩` and its frames, empty memory,
heap use 0 (`hhu`), its allocation count `th₀.nalloc` fresh from the static
placement (`hfr0`); and `H` holding at the loaded state with no range held,
`hH0`, in place of `HeldOk`'s phase). -/
theorem pre_loadAH {Λ : Scc.Sem.Layout} {G : Loc → Val → Prop} {own : OwnS} {I : InvS} {μ : Marks}
    {H : State → List (Nat × Range) → Prop}
    {tcells : List (Directive × Nat)} {syms : List (String × Nat)} {mem : List (Loc × Val)} {lsize : Lsize}
    {secs : DataSecs}
    {code : String → Option Nat} {name : WeakMem.AllocLabel → String} {s₀ : TermRun.Cfg} {th₀ : TermRun.TTh}
    (himg : imageOk Λ secs code = true) (hss : StaticSyms Λ secs code lsize name)
    (hw : wideIn (tcells.map (·.1)) = true)
    (hinit : P.init s₀) (hs0 : s₀.ths = #[th₀]) (hσ : th₀.σs = []) (hp : th₀.promises = [])
    (hsm : s₀.mem = #[]) (hhu : heapUse s₀ = 0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo tcells syms) ⟨th₀.term, th₀.env, none⟩ th₀.stack)
    (hfr0 : AllocInv.FreshInv Λ.static s₀.lbase s₀.n 0 th₀.nalloc)
    (hmem : ∀ q ∈ mem, InitIn Λ q.1) (hmf : ∀ q ∈ mem, q.2.toNat < 2 ^ 64)
    (hH0 : H (threadAt E Λ.code.lo tcells syms) [])
    (hown0 : OwnInit (own (threadAt E Λ.code.lo tcells syms) th₀.stack)
      (loadProg (kernel 1) E Λ tcells syms mem).1.mem)
    (hg : MemInv G (loadProg (kernel 1) E Λ tcells syms mem).1.mem) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      (loadProg (kernel 1) E Λ tcells syms mem).1.mem.initVal (wordLoc a) = 0)
    (hc0 : (loadProg (kernel 1) E Λ tcells syms mem).1.mem.initVal (wordLoc ar.ctr) = 0) :
    PreSAH Λ P p G own I H μ ar (loadProg (kernel 1) E Λ tcells syms mem) s₀ := by
  have hinv : Inv1 Λ Λ.static lsize (fun _ => none) (Thread.init (threadAt E Λ.code.lo tcells syms) : Thread isa)
      (loadProg (kernel 1) E Λ tcells syms mem).1.mem s₀.mem := by
    rw [hsm]; exact Inv1.start_static himg hss rfl rfl
  refine ⟨Thread.init (threadAt E Λ.code.lo tcells syms), th₀, 0, Λ.static, lsize, fun _ => none, [], ∅, none,
    rfl, ?_, fun _ => by simp [Kernel.byte],
    hH0, .inl rfl, certOkC_of_prom_nil rfl, hs0, hσ, hp, hst, .inl trivial,
    wideSt_threadAt hw _ _ _,
    bnd_init _ _,
    hinv, ?_, ⟨?_, hmem⟩, ⟨fits_empty rfl, hmf⟩, hg,
    ownOk_init (by simp [loadProg, Config.init]) hown0 _, ?_, hfr0, ?_,
    [], s₀, hinit, .refl _⟩
  · exact ⟨E, rfl⟩
  · intro k m hk; unfold Memory.get? at hk; split at hk
    · cases hk
    · simp [loadProg, Config.init] at hk
  · intro k m hk; unfold Memory.get? at hk; split at hk
    · cases hk
    · simp [loadProg, Config.init] at hk
  · have hnm : ∀ k', (loadProg (kernel 1) E Λ tcells syms mem).1.mem.get? k' = none := fun k' => by
      cases hk : (loadProg (kernel 1) E Λ tcells syms mem).1.mem.get? k' with
      | none => rfl
      | some m =>
        unfold Memory.get? at hk; split at hk
        · cases hk
        · simp [loadProg, Config.init] at hk
    have har : AllocRow.ArenaOK Λ Λ.static lsize (Thread.init (threadAt E Λ.code.lo tcells syms) : Thread isa)
        (loadProg (kernel 1) E Λ tcells syms mem).1.mem ar.heap ar.cells 0 (fun _ => False) := by
      rw [hstat]; exact AllocRow.ArenaOK.init hsub hal hz0 hnm
    have hct := AllocInv.CtrAt.init (prom := (Thread.init (threadAt E Λ.code.lo tcells syms) : Thread isa).prom)
      (ctr := ar.ctr) (fun k' _ => hnm k')
    rw [hc0] at hct
    rw [hhu]
    exact .inr ⟨(fun w h => by cases h), by simpa using hct, har⟩
  · intro l b hb
    simp [hstat] at hb

/-- **The site's range is fresh** at the take (`fresh_of` with the held
ranges `hl`, each off the range, `HeldPathS.held`). -/
theorem fresh_ofH (hwf : Λ.WF) {r : Range} {t : T.M.Cfg} {j : Nat} {hl : List (Nat × Range)}
    {pm : _root_.Mem 64} (hk : t.2 = KS E Λ j hl pm) (hsub : r.Sub Λ.stackPool) (hpos : 0 < r.size)
    (hrod : Λ.rodata.Disjoint Λ.stackPool) (hdj : ∀ h ∈ hl, r.Disjoint h.2) (hmi : MemIn Λ t.1.mem) :
    Kernel.fresh t r = true := by
  have hall : hl.all (fun h => !Kernel.overlaps r h.2.lo h.2.size) = true := by
    rw [List.all_eq_true]
    intro x hx
    rcases hdj x hx with h | h <;> simp [Kernel.overlaps] <;> omega
  have h0 := fresh_of (E := E) (t := (t.1, KS E Λ j [] pm)) hwf rfl hsub hpos hrod hmi
  unfold Kernel.fresh at h0 ⊢
  rw [hk]
  have e : (KS E Λ j hl pm).held = hl := rfl
  have e0 : (KS E Λ j [] pm).held = [] := rfl
  have ep : (KS E Λ j hl pm).pool = (KS E Λ j [] pm).pool := rfl
  rw [e, ep, hall]
  rw [e0] at h0
  simpa using h0

/-- **No promise at a `write`** at any depth (`WriteNoPromS` over `PreSA`). Over `HeldPathS`. -/
def WriteNoPromAH (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS)
    (I : InvS) (H : State → List (Nat × Range) → Prop) (μ : Marks) (ar : Arena) : Prop :=
  ∀ t s th, PreSAH Λ P p G own I H μ ar t s → t.1.threads = #[th] → abi.atSys th.st = true →
    (∃ fd buf n, Kernel.callOf abi th = some (.write fd buf n)) → th.prom = []

/-- **`RS` is explicit** (`r_components` with the frames). Over `HeldPathS`. -/
theorem r_componentsAH {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab)
    (hwf : Λ.WF) {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H) {t : T.M.Cfg}
    {s : TermRun.Cfg} (h : RSAH Λ P p G own I H μ ar t s) :
    ∃ w : Witness T.M, Components T.M Λ w t ((SrcSem.source P p).core s) := by
  rcases h with ⟨th, th0, j, lbl, lsize, ts, hl, pm, _, hth, ⟨E, hk⟩, -, hh, -, -, hs0, -, -, hI, -, -, -, hinv,
      hown, hmi, -⟩ |
    ⟨th, th0, j, lbl, lsize, ts, hl, pm, o, hth, ⟨E, hk⟩, -, hh, hs0, -, -, hpl, hinv, hown, hmi, -⟩
  · exact (components_oneSXH hwf hth (by rw [hk]; rfl) (hT.own _ _ hh) hmi hs0
      (by have hpl := hN.place _ _ _ _ _ hI; exact hpl) hinv hown).imp fun _ h => h.1
  · exact (components_oneSXH hwf hth (by rw [hk]; rfl) (hT.own _ _ hh) hmi hs0 hpl hinv hown).imp fun _ h => h.1

/-- The memory of a configuration `RS` relates is in the layout. Over `HeldPathS`. -/
theorem r_memInAH {H : State → List (Nat × Range) → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : RSAH Λ P p G own I H μ ar t s) : MemIn Λ t.1.mem := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmi, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmi, _⟩ <;> exact hmi

end Spike.Lib.X64ConsumerA

/-! ## Axiom guards -/

/--
info: 'Spike.Lib.X64ConsumerS.AbortPathS.toC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerS.AbortPathS.toC

/--
info: 'Spike.Lib.X64ConsumerA.pre_loadAH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.pre_loadAH

/--
info: 'Spike.Lib.X64ConsumerA.fresh_ofH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.fresh_ofH

/--
info: 'Spike.Lib.X64ConsumerA.r_componentsAH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.r_componentsAH

/--
info: 'Spike.Lib.X64ConsumerA.r_memInAH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.r_memInAH
