/-
**The source's numbers from either start** of an `Accepted2` program
(ISA-neutral): `SrcSem.progInit` starts before the setup block
(`setupStart`) or, with none, at `main` on `()` (`mainStart`); both keep
`invN_reach`'s invariant. The setup block's facts come from its result's
words (`Scc.Obj.valWords`, which the lowering checks); its result is not a
bare locative by `Accepted2` (`hloc_of_accepted2`).

- `invN_initU`: `mainStart` keeps the invariant (no setup block).
- `invN_progInit`: every start of `progInit` keeps it.
- `setup_simpleTy`, `hset_of_valWords`: the setup result's `Compat`.
- `invN_reachP`, `srcNumS_of_accepted2P`, `srcRd_isNumP`: `invN_reach`,
  `srcNumS_of_accepted2`, `srcRd_isNum` from `progInit`, with no setup
  premise.
-/
import Spike.Lib.Src.SrcRdNum
import Spike.Lib.Src.Accepted2Out

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm TermRun Scc.Sem
open TermFul (promsOf promsOf_some)
open Scc.Lower (litWalks2 shapeOf simpleTy Accepted2 setupOf decl2)
open Scc.Sem.SrcSem
open Spike.Lib.Consumer1 (SrcRd)

/-- **The start at `main` keeps the invariant** (no setup block): no
message, the tail call of `main` on `()` with no frame. -/
theorem invN_initU {p : Prog} (hs : setupOf p = none) (cap : Nat) :
    InvN p { mainStart with cap := cap } := by
  refine ⟨⟨rfl, fun k m hk _ => by simp [mainStart] at hk⟩,
    fun i => ⟨fun q hq => by simp [mainStart] at hq, fun t ht => ?_⟩, _, rfl,
    rfl, .unit, Or.inr (Or.inr ⟨Or.inl (Or.inr ⟨hs, rfl, rfl⟩), rfl⟩), trivial⟩
  rcases i with _ | i <;> simp [promsOf, mainStart] at ht

/-- **Every start of an `Accepted2` program keeps the invariant**: before
the setup block (`invN_init`) or at `main` (`invN_initU`). -/
theorem invN_progInit {p : Prog} (hacc : Accepted2 p = true) {cap : Nat} {c : Cfg} (h : progInit p cap c) :
    InvN p c := by
  cases hs : setupOf p with
  | none =>
    rw [progInit_of_setupOf_none hacc hs] at h
    subst h
    exact invN_initU hs cap
  | some s =>
    rw [progInit_of_setupOf_some hs] at h
    obtain ⟨meW, rfl⟩ := h
    exact invN_init hs cap meW

/-- **The setup result is `simpleTy`** (`setup2`). -/
theorem setup_simpleTy {p : Prog} (hacc : Accepted2 p = true) {s : Ty} (hs : setupOf p = some s) :
    simpleTy s = true := by
  obtain ⟨hds, hsp, -⟩ := accepted2_parts hacc
  have hany : p.any (·.name == "rodata") = true := by
    simpa [Scc.Lower.setupPresent, hs] using hsp
  obtain ⟨d, hd, hname⟩ : ∃ d ∈ p, d.name = "rodata" := by
    obtain ⟨d, hd, hn⟩ := List.any_eq_true.1 hany
    exact ⟨d, hd, by simpa using hn⟩
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds d hd
  unfold decl2 at hE
  split at hE
  · simp only [Bool.and_eq_true] at hE
    have := Scc.Frontend.declIs_eq hE.1; subst this; exact absurd hname (by decide)
  · split at hE
    · rename_i hx; simp [hname] at hx
    · split at hE
      · rename_i hm; simp [hname] at hm
      · split at hE
        · rename_i s' hs'
          rw [hs] at hs'; cases hs'
          simp only [hname, beq_self_eq_true, ↓reduceIte, Scc.Lower.setup2, Bool.and_eq_true, beq_iff_eq] at hE
          exact hE.1.2.1
        · rename_i hs'; rw [hs] at hs'; cases hs'

/-- **The setup result has its own layout** given its words (which the
lowering checks: `rodata`'s result has a runtime layout). -/
theorem hset_of_valWords {p : Prog} (hacc : Accepted2 p = true)
    (hv : ∀ s, setupOf p = some s → ∃ k, Scc.Obj.valWords s = some k) :
    ∀ s, setupOf p = some s → Compat s (shapeOf s) = true := fun s hs =>
  have ⟨_, hk⟩ := hv s hs
  compat_shapeOf_self (setup_simpleTy hacc hs) hk

/-- **Every reachable configuration keeps the invariant** from either start
(`invN_progInit`). -/
theorem invN_reachP {P : SrcParams} {p : Prog} (hacc : Accepted2 p = true)
    (hn : ∀ q ∈ litWalks2 p, numQ q = true) (hv : ∀ s, setupOf p = some s → ∃ k, Scc.Obj.valWords s = some k)
    (hinit : ∀ c, P.init c → progInit p P.cap c)
    (hH : P.hooks = SrcHooks.none ∨ SrcOutProto.UsesWc P p)
    {tr : List Ev} {s : Cfg} (h : (source P p).Reach tr s) : InvN p s := by
  obtain ⟨c0, h0, hrun⟩ := h
  exact invN_run hacc (hset_of_valWords hacc hv) (goodBlocks_of hacc hn) hH hrun
    (invN_progInit hacc (hinit c0 h0))

/-- **The printed cells of an `Accepted2` program hold numbers** from either
start (`srcNumS_of_accepted2` with `invN_reachP`). -/
theorem srcNumS_of_accepted2P {P : SrcParams} {p : Prog} (hacc : Accepted2 p = true)
    (hn : ∀ q ∈ litWalks2 p, numQ q = true) (hv : ∀ s, setupOf p = some s → ∃ k, Scc.Obj.valWords s = some k)
    (hinit : ∀ c, P.init c → progInit p P.cap c)
    (hH : P.hooks = SrcHooks.none ∨ SrcOutProto.UsesWc P p) : SrcNumSP P p PrintLd := by
  intro tr s th hr hth hp c1 ht he c' l j hl hld
  obtain ⟨hN, -, th0, h0, hT⟩ := invN_reachP hacc hn hv hinit hH hr
  rw [hth] at h0; cases h0
  exact hN.latest hth hp (thN_hcell hacc (hset_of_valWords hacc hv) hT ht he hl hld)

/-- **The source's reads are numbers** for an `Accepted2` program from either
start (`srcRd_isNum` with `invN_reachP`). -/
theorem srcRd_isNumP {P : SrcParams} {p : Prog} (hacc : Accepted2 p = true)
    (hn : ∀ q ∈ litWalks2 p, numQ q = true) (hv : ∀ s, setupOf p = some s → ∃ k, Scc.Obj.valWords s = some k)
    (hinit : ∀ c, P.init c → progInit p P.cap c)
    (hH : P.hooks = SrcHooks.none ∨ SrcOutProto.UsesWc P p) : SrcRd P p IsNum := by
  intro tr s th k m lbl x hr hs hp hm hrep
  obtain ⟨⟨-, hnp⟩, -, -⟩ := invN_reachP hacc hn hv hinit hH hr
  have hth : s.ths[0]? = some th := by rw [hs]; rfl
  obtain ⟨n, hv'⟩ := hnp k m hm (by rw [promsOf_some hth, hp]; exact List.not_mem_nil)
  refine ⟨n, hv', ?_⟩
  have h := hrep
  rw [hv'] at h
  exact h.1

/-- info: 'Spike.Lib.LowerNode.srcRd_isNumP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms srcRd_isNumP

/-- info: 'Spike.Lib.LowerNode.srcNumS_of_accepted2P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms srcNumS_of_accepted2P

end Spike.Lib.LowerNode
