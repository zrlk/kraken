/-
**The whole-program lowering of an `Accepted1` program** (calls between
code blocks, any number of code blocks), from the closed form `lowerC`
(`Scc/Lower/InvC1.lean`): the runtime functions, then `func1` of each code
block in program order, and the traces `marks1`.

- `checkedOf_accepted1`: the checked program: entry `main(Unit) : Int`, no
  externs (`externs_accepted1`);
- `lowerWithMarks_accepted1[_ok]`, `lowerIR_accepted1`: the whole-program
  statements, as `Scc/Lower/InvProg.lean`'s for `Accepted0`;
- `Pairwise2`: two lists related pairwise (core Lean has no `Forall₂`);
- `mem_progOf_zipIdx`, `mem_progOf_funcs1`: code block `i`'s function
  `func1 … rs[i]` is at index `rt.length + i` of the program's functions;
- `find_index`: a declaration `find?` finds is one at an index.

ISA-free: the x86-64 modules import it too (`Spike/Lib/LowerProgC1.lean`
adds the AArch64 `lowerAll_accepted1_a64` and imports the AArch64 lowering,
which the x86-64 syntax cannot be imported with).
-/
import Scc.Lower.InvC1
import Scc.Lower.InvProg

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc Scc.IR
open Scc.Lower
open Scc.Lower.Inv

/-- An `Accepted1` body spawns nothing. -/
theorem spawnedE_of_body1 (earlier : List String) :
    ∀ (e : Expr) (scope : List String), body1 earlier scope e = true → spawnedE e = [] := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope hb
    cases op <;> simp only [body1, Bool.and_eq_true, reduceCtorEq] at hb <;>
      first
      | (simp only [spawnedE]; exact ih _ hb.2)
      | simp at hb
  | ifeq a b y n ihy ihn =>
    intro scope hb
    simp only [body1, Bool.and_eq_true] at hb
    simp only [spawnedE, ihy _ hb.1.2, ihn _ hb.2, List.append_nil]
  | ret a => intro _ _; rfl
  | _ => intro scope hb; simp [body1] at hb

/-- Each code block of a `decls1` list is `decl1` for some earlier names. -/
theorem decl1_of_decls1 : ∀ (ds : Prog) (earlier : List String), decls1 earlier ds = true →
    ∀ d ∈ ds, ∃ earlier', decl1 earlier' d = true
  | [], _, _, _, hd => by cases hd
  | d :: ds, earlier, h, d', hd' => by
    simp only [decls1, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hd' with rfl | hm
    · exact ⟨_, h.1⟩
    · exact decl1_of_decls1 ds _ h.2 d' hm

theorem decls1_of_accepted1 {p : Prog} (hp : Accepted1 p = true) : decls1 [] p = true := by
  simp only [Accepted1, Bool.and_eq_true] at hp
  exact hp.1.2

/-- An `Accepted1` program spawns nothing. -/
theorem spawned_accepted1 {p : Prog} (hp : Accepted1 p = true) : p.flatMap (fun d => spawnedE d.body) = [] := by
  simp only [List.flatMap_eq_nil_iff]
  intro d hd
  obtain ⟨e, he⟩ := decl1_of_decls1 p [] (decls1_of_accepted1 hp) d hd
  exact spawnedE_of_body1 e _ _ (decl1_shape he).2.2

/-- **The checked program of an `Accepted1` program**: entry `main(Unit) :
Int`, no externs. -/
theorem checkedOf_accepted1 {p : Prog} (hp : Accepted1 p = true) :
    checkedOf p = .ok { prog := p, entry := ⟨.unit, true⟩, externs := [], adds := [] } := by
  have hm : p.any (·.name == "main") = true := by
    simp only [Accepted1, Bool.and_eq_true] at hp
    exact hp.1.1.2
  obtain ⟨dm, hf⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr (List.any_eq_true.mp hm) : (p.find? (·.name == "main")).isSome)
  have hn : dm.name = "main" := by simpa using List.find?_some hf
  obtain ⟨e, he⟩ := decl1_of_decls1 p [] (decls1_of_accepted1 hp) dm (List.mem_of_find?_eq_some hf)
  have he' := he
  simp only [decl1, hn, beq_self_eq_true, ite_true, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at he'
  obtain ⟨⟨⟨⟨ht, hi⟩, hr⟩, ha⟩, -⟩ := he'
  simp [checkedOf, Scc.Frontend.entryOf, hf, ht, hi, ha, hr, externs_accepted1 hp,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- **Two lists related pairwise** by `P`: of one length, `P` on each pair
of `ds.zip rs`. -/
def Pairwise2 {α γ : Type} (P : α → γ → Prop) (ds : List α) (rs : List γ) : Prop :=
  rs.length = ds.length ∧ ∀ dr ∈ ds.zip rs, P dr.1 dr.2

/-- `Pairwise2` at an index. -/
theorem Pairwise2.get {α γ : Type} {P : α → γ → Prop} {ds : List α} {rs : List γ} (h : Pairwise2 P ds rs)
    (i : Nat) (hi : i < ds.length) : P ds[i] (rs[i]'(h.1 ▸ hi)) :=
  h.2 (ds[i], rs[i]'(h.1 ▸ hi)) (List.mem_iff_getElem.mpr ⟨i, by simp [h.1, hi], by simp⟩)

/-- `mapM` of a function that succeeds on each element with a witness. -/
theorem mapM_ok_of {α β γ ε : Type} {f : α → Except ε β} {P : α → γ → Prop} {F : α → γ → β} :
    ∀ ds : List α, (∀ d ∈ ds, ∃ r, P d r ∧ f d = .ok (F d r)) →
      ∃ rs, Pairwise2 P ds rs ∧ ds.mapM f = .ok (List.zipWith F ds rs)
  | [], _ => ⟨[], ⟨rfl, by simp⟩, rfl⟩
  | d :: ds, h => by
    obtain ⟨r, hr, hf⟩ := h d (by simp)
    obtain ⟨rs, ⟨hl, hrs⟩, hm⟩ := mapM_ok_of ds (fun x hx => h x (by simp [hx]))
    refine ⟨r :: rs, ⟨by simp [hl], ?_⟩, ?_⟩
    · intro dr hdr
      simp only [List.zip_cons_cons, List.mem_cons] at hdr
      rcases hdr with rfl | hdr
      · exact hr
      · exact hrs dr hdr
    · simp [List.mapM_cons, hf, hm, bind, Except.bind, pure, Except.pure]

/-- The closed form of code block `d` of `p` (`lowerC`), with depth limit
`frames`. -/
abbrev LowC (p : Prog) (obj : Scc.ObjLayout) (frames : Option Nat) (d : Decl) (r : Res1) : Prop :=
  lowerC { prog := p, externs := [], fn := d.name, obj, frames } (env1 d) 0 "entry" 0 d.body = some r

/-- The user functions of an `Accepted1` program, for the closed forms `rs`. -/
def funcs1 (p : Prog) (rs : List Res1) : List Func :=
  List.zipWith (fun d r => func1 (Names.user d.name) (params1R d) r) p rs

/-- The placement traces of an `Accepted1` program, for the closed forms `rs`. -/
def marksAll1 (p : Prog) (rs : List Res1) : List (Sym × Array (Node × Point)) :=
  List.zipWith (fun d r => (Names.user d.name, marks1 d r)) p rs

/-- The code blocks of an `Accepted1` program lower to `funcs1` with the
traces `marksAll1`. -/
theorem mapM_lowerDeclMarks_accepted1 {p : Prog} (hp : Accepted1 p = true) (obj : Scc.ObjLayout)
    (frames : Option Nat) :
    ∃ rs, Pairwise2 (LowC p obj frames) p rs ∧
      p.mapM (fun d => lowerDeclMarks p [] d obj frames) =
        .ok (List.zipWith (fun d r => (func1 (Names.user d.name) (params1R d) r, marks1 d r)) p rs) := by
  have h := accepted1_lowerC hp obj frames
  rw [externs_accepted1 hp] at h
  exact mapM_ok_of p h

/-- **The whole-program lowering of an `Accepted1` program**: the runtime
functions, then `funcs1`; the traces `marksAll1`. -/
theorem lowerWithMarks_accepted1 (cfg : Config) {p : Prog} (hp : Accepted1 p = true)
    (hheap : cfg.layout.heapBytes < 2 ^ 32) {rt : List Func}
    (hrt : rtFuncs cfg.layout ⟨.unit, true⟩ 0 = .ok rt) :
    ∃ rs, Pairwise2 (LowC p cfg.layout.obj none) p rs ∧
      lowerWithMarks cfg { prog := p, entry := ⟨.unit, true⟩, externs := [], adds := [] } =
        .ok (progOf cfg.layout rt (funcs1 p rs), marksAll1 p rs) := by
  obtain ⟨rs, hrs, hm⟩ := mapM_lowerDeclMarks_accepted1 hp cfg.layout.obj none
  refine ⟨rs, hrs, ?_⟩
  have hh : ¬ (cfg.layout.heapBytes ≥ 2 ^ 32) := by omega
  unfold rtFuncs at hrt
  have hf : p.filter (fun d => !(([] : List (String × Frontend.Extern)).any (·.1 == d.name))) = p := by simp
  simp only [lowerWithMarks, hh, ite_false, hf, hm, spawned_accepted1 hp, List.eraseDups_nil, List.mapM_nil, hrt,
    bind, Except.bind, pure, Except.pure]
  simp [progOf, funcs1, marksAll1, func1]

/-- A successful `lowerWithMarks` of an `Accepted1` program is the one of
`lowerWithMarks_accepted1`. -/
theorem lowerWithMarks_accepted1_ok (cfg : Config) {p : Prog} (hp : Accepted1 p = true)
    {x : IR.Program × List (Sym × Array (Node × Point))}
    (h : lowerWithMarks cfg { prog := p, entry := ⟨.unit, true⟩, externs := [], adds := [] } = .ok x) :
    ∃ rs rt, Pairwise2 (LowC p cfg.layout.obj none) p rs ∧
      rtFuncs cfg.layout ⟨.unit, true⟩ 0 = .ok rt ∧
      x = (progOf cfg.layout rt (funcs1 p rs), marksAll1 p rs) := by
  have hheap : cfg.layout.heapBytes < 2 ^ 32 := by
    refine Nat.lt_of_not_ge fun hc => ?_
    unfold lowerWithMarks at h
    simp only [hc, ↓reduceIte] at h
    cases h
  cases hrt : rtFuncs cfg.layout ⟨.unit, true⟩ 0 with
  | error e =>
    exfalso
    obtain ⟨rs, -, hm⟩ := mapM_lowerDeclMarks_accepted1 hp cfg.layout.obj none
    have hh : ¬ (cfg.layout.heapBytes ≥ 2 ^ 32) := by omega
    unfold rtFuncs at hrt
    have hf : p.filter (fun d => !(([] : List (String × Frontend.Extern)).any (·.1 == d.name))) = p := by simp
    simp only [lowerWithMarks, hh, ite_false, hf, hm, spawned_accepted1 hp, List.eraseDups_nil, List.mapM_nil,
      hrt, bind, Except.bind, pure, Except.pure] at h
    cases h
  | ok rt =>
    obtain ⟨rs, hrs, hl⟩ := lowerWithMarks_accepted1 cfg hp hheap hrt
    rw [hl] at h
    cases h
    exact ⟨rs, rt, hrs, rfl, rfl⟩

/-- **The lowering `lowerAll` starts from, on an `Accepted1` program**: the
runtime functions, then `func1` of each code block (`funcs1`), each from its
closed form `lowerC` without the depth counter (`frames = none`); the traces
`marksAll1`. -/
theorem lowerIR_accepted1 (cfg : Config) {p : Prog} (hp : Accepted1 p = true)
    {l : Lowered} (hl : lowerIR cfg p = .ok l) :
    ∃ rs rt, Pairwise2 (LowC p cfg.layout.obj none) p rs ∧
      rtFuncs cfg.layout ⟨.unit, true⟩ 0 = .ok rt ∧
      l.ir = progOf cfg.layout rt (funcs1 p rs) ∧ l.marks = marksAll1 p rs := by
  unfold lowerIR at hl
  rw [checkedOf_accepted1 hp] at hl
  simp only [bind, Except.bind] at hl
  cases hb : stackBudget cfg { prog := p, entry := ⟨.unit, true⟩, externs := [], adds := [] } with
  | error e => rw [hb] at hl; cases hl
  | ok b =>
    rw [hb] at hl
    cases hw : lowerWithMarks cfg { prog := p, entry := ⟨.unit, true⟩, externs := [], adds := [] } with
    | error e => simp only [hw] at hl; cases hl
    | ok x =>
      obtain ⟨rs, rt, hrs, hrt, rfl⟩ := lowerWithMarks_accepted1_ok cfg hp hw
      simp only [hw] at hl
      cases hl
      exact ⟨rs, rt, hrs, hrt, rfl, rfl⟩

/-- **The `i`-th further function is at index `rt.length + i`** of the
program's functions. -/
theorem mem_progOf_zipIdx (lay : Layout) (rt fs : List Func) (i : Nat) (h : i < fs.length) :
    (fs[i], rt.length + i) ∈ (progOf lay rt fs).funcs.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?]
  simp [progOf, h]

/-- **Code block `i`'s function is at index `rt.length + i`** of the
program's functions: `func1` of its closed form `rs[i]`. -/
theorem mem_progOf_funcs1 (lay : Layout) (rt : List Func) {p : Prog} {rs : List Res1} {P : Decl → Res1 → Prop}
    (h : Pairwise2 P p rs) (i : Nat) (hi : i < p.length) :
    (func1 (Names.user p[i].name) (params1R p[i]) (rs[i]'(h.1 ▸ hi)), rt.length + i) ∈
      (progOf lay rt (funcs1 p rs)).funcs.zipIdx := by
  have hl : i < (funcs1 p rs).length := by simp [funcs1, h.1, hi]
  have := mem_progOf_zipIdx lay rt (funcs1 p rs) i hl
  simpa [funcs1] using this

/-- **A declaration `find?` finds is one at an index.** -/
theorem find_index {p : Prog} {g : String} {d' : Decl} (h : p.find? (·.name == g) = some d') :
    ∃ i, ∃ hi : i < p.length, p[i] = d' :=
  List.mem_iff_getElem.mp (List.mem_of_find?_eq_some h)

end Spike.Lib.LowerNode
