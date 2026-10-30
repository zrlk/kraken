/-
**The whole-program lowering of an `Accepted2` program** (ISA-free), from
the closed form `lowerC2` (`Spike/Lib/LowerShapeC2.lean`): the runtime
functions, then `func2` of each compiled code block (every block but the
output extern and its loop) in program order, and the traces `marks2`.

- `compiled2`, `entry2`, `checked2`, `setupWords2`: the compiled blocks, the
  entry shape, the checked program and the setup result's words as
  `checkedOf` and `lowerWithMarks` compute them;
- `checkedOf_accepted2`: the checked program is `checked2 p`;
- `spawned_accepted2`: an `Accepted2` program spawns nothing;
- `Low2`, `LowC2`, `funcs2`, `marksAll2`: a code block's lowering data and
  closed form, the user functions and the traces;
- `mapM_ok_inv`: a successful `mapM`, element by element;
- `lowerDeclMarks_low2`: each compiled block's lowering is `func2` of its
  closed form (`accepted2_lowerC2`, `lowerDeclMarks_lowerC2`);
- `lowerWithMarks_accepted2_ok`, `lowerIR_accepted2`: a successful lowering
  is `progOf … (funcs2 p ws)` with the traces `marksAll2 p ws`;
- `mem_progOf_funcs2`: compiled block `i`'s function is at index
  `rt.length + i`.

The statements take the lowering's success (from `placeOKAt`, as
`lowerAll?_ok_of_placeOK`): `lowerC2`'s operand shapes follow from it,
not from `Accepted2` alone. `Spike/Lib/LowerProgC2.lean` and
`Spike/Lib/LowerX64/LowerProgC2X.lean` add `lowerAll`'s IR on each ISA.
-/
import Spike.Lib.LowerShapeC2Some
import Spike.Lib.LowerProgC1Core
import Spike.Lib.Src.XchgLeaf

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc Scc.IR
open Scc.Lower
open Scc.Lower.Inv
open Spike.Lib.LowerShape

/-- **The compiled code blocks** of a program: those not among the frontend's
externs (`lowerWithMarks`' `compiled`). -/
def compiled2 (p : Prog) : Prog := p.filter fun d => !((Frontend.externs p).any (·.1 == d.name))
/-- The entry shape of an `Accepted2` program: `main` takes the setup
result and its thread word when `setupOf p` is set, else `Unit`; it returns
an `Int`. -/
def entry2 (p : Prog) : Frontend.Entry := ⟨if (setupOf p).isSome then .setupTid else .unit, true⟩
/-- **The checked program of an `Accepted2` program** (`checkedOf_accepted2`). -/
def checked2 (p : Prog) : Frontend.Checked :=
  { prog := p, entry := entry2 p, externs := Frontend.externs p, adds := [] }
/-- The setup result's words `lowerWithMarks` passes `mainThreadF`: the
value words of the setup block `rodata`'s result with a setup block, else
`0`. -/
def setupWords2 (p : Prog) : Nat :=
  if (setupOf p).isSome then ((p.find? (·.name == "rodata")).bind fun r => Obj.valWords r.retTy).getD 0 else 0

/-- **A code block's lowering data**: its argument words `na`, the parameter
registers' scalar and trace marks `sc`, `hp` (`markR`), its body's closed
form `r` (`lowerC2`). -/
structure Low2 where
  na : Nat
  sc : List Reg
  hp : List Reg
  r : Res2

/-- **The closed form of code block `d` of `p`** (`lowerC2`, no depth
counter), with its argument's word count and marks. -/
def LowC2 (p : Prog) (obj : ObjLayout) (d : Decl) (w : Low2) : Prop :=
  Obj.valWords d.argTy = some w.na ∧ markR d.argTy ((paramsR d w.na).map .reg) = some (w.sc, w.hp) ∧
    lowerC2 { prog := p, externs := Frontend.externs p, fn := d.name, obj } (env2 d w.na) 0 "entry" 0 d.body =
      some w.r

/-- The user functions of an `Accepted2` program for the lowering data
`ws`, one per compiled code block in program order. -/
def funcs2 (p : Prog) (ws : List Low2) : List Func :=
  List.zipWith (fun d w => func2 (Names.user d.name) (paramsR d w.na) w.sc w.hp w.r) (compiled2 p) ws

/-- The placement traces of an `Accepted2` program for the lowering data `ws`. -/
def marksAll2 (p : Prog) (ws : List Low2) : List (Sym × Array (Node × Point)) :=
  List.zipWith (fun d w => (Names.user d.name, marks2 d w.na w.r)) (compiled2 p) ws

/-- An `Accepted2` body spawns nothing. -/
theorem spawnedE_of_body2 (cx : Cx2) : ∀ (e : Expr) (cs bufs : List (String × Nat)) (scope : List String),
    body2 cx cs bufs scope e = true → spawnedE e = [] := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro cs bufs scope hb
    cases op
    all_goals first
      | (simp [body2] at hb; done)
      | skip
    all_goals simp only [spawnedE]
    all_goals first
      | (simp only [body2, Bool.and_eq_true] at hb; exact ih _ _ _ hb.2)
      | skip
    · rename_i n τ
      simp only [body2, Bool.and_eq_true] at hb
      revert hb; split
      · intro hb; simp only [Bool.and_eq_true] at hb; exact ih _ _ _ hb.2.2
      · simp
    · rename_i b i v
      revert hb
      cases b <;> cases i <;> simp only [body2, Bool.and_eq_true, Bool.false_eq_true, false_implies]
      all_goals (intro hb; exact ih _ _ _ hb.2)
  | ifeq a b y n ihy ihn =>
    intro cs bufs scope hb
    simp only [body2, Bool.and_eq_true] at hb
    simp only [spawnedE, ihy _ _ _ hb.1.2, ihn _ _ _ hb.2, List.append_nil]
  | split a x y e ih =>
    intro cs bufs scope hb
    simp only [body2, Bool.and_eq_true] at hb
    exact ih _ _ _ hb.2
  | unpack a i x e ih =>
    intro cs bufs scope hb
    simp only [body2, Bool.and_eq_true] at hb
    exact ih _ _ _ hb.2
  | ret a => intro _ _ _ _; rfl
  | _ => intro cs bufs scope hb; simp [body2] at hb

/-- **An `Accepted2` program spawns nothing**: the extern and its loop
spawn nothing either. -/
theorem spawned_accepted2 {p : Prog} (hp : Accepted2 p = true) : p.flatMap (fun d => spawnedE d.body) = [] := by
  have hds : decls2 [] (setupOf p) (hasPrint p) p = true := by
    simp only [Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.2
  simp only [List.flatMap_eq_nil_iff]
  intro d hd
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds d hd
  unfold decl2 at hE
  split at hE
  · simp only [Bool.and_eq_true] at hE
    rw [Frontend.declIs_eq hE.1]; rfl
  split at hE
  · rw [Frontend.declIs_eq hE]; rfl
  split at hE
  · unfold main2 at hE
    simp only [Bool.and_eq_true] at hE
    exact spawnedE_of_body2 _ d.body _ _ _ hE.2
  split at hE
  · split at hE
    · unfold setup2 at hE
      simp only [Bool.and_eq_true] at hE
      exact spawnedE_of_body2 _ d.body _ _ _ hE.2
    · unfold plain2 at hE
      simp only [Bool.and_eq_true] at hE
      exact spawnedE_of_body2 _ d.body _ _ _ hE.2
  · unfold plain2 at hE
    simp only [Bool.and_eq_true] at hE
    exact spawnedE_of_body2 _ d.body _ _ _ hE.2

/-- **The checked program of an `Accepted2` program**: entry `main` taking
`Unit`, or the setup result and its thread word; the frontend's externs. -/
theorem checkedOf_accepted2 {p : Prog} (hp : Accepted2 p = true) : checkedOf p = .ok (checked2 p) := by
  have hds : decls2 [] (setupOf p) (hasPrint p) p = true := by
    simp only [Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.2
  have hsp : setupPresent p = true := by
    simp only [Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.2
  have hm : p.any (·.name == "main") = true := by
    simp only [Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.1.2
  obtain ⟨dm, hf⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr (List.any_eq_true.mp hm) : (p.find? (·.name == "main")).isSome)
  have hn : dm.name = "main" := by simpa using List.find?_some hf
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds dm (List.mem_of_find?_eq_some hf)
  have hpe : isPrintExt dm = false := by simp [isPrintExt, hn]
  have hnl : (hasPrint p && "main" == "printL") = false := by simp
  simp only [decl2, hpe, hn, hnl, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at hE
  unfold main2 at hE
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hE
  obtain ⟨⟨⟨⟨ht, hi⟩, hr⟩, ha⟩, -⟩ := hE
  cases hs : setupOf p with
  | none =>
    simp only [hs] at ha
    rw [beq_iff_eq] at ha
    simp [checkedOf, Scc.Frontend.entryOf, hf, ht, hi, ha, hr, checked2, entry2, hs,
      Except.mapError, bind, Except.bind, pure, Except.pure]
  | some st =>
    simp only [hs] at ha
    rw [beq_iff_eq] at ha
    have hrm : p.any (·.name == "rodata") = true := by simpa [setupPresent, hs] using hsp
    obtain ⟨dr, hfr⟩ := Option.isSome_iff_exists.mp
      (List.find?_isSome.mpr (List.any_eq_true.mp hrm) : (p.find? (·.name == "rodata")).isSome)
    have hrn : dr.name = "rodata" := by simpa using List.find?_some hfr
    obtain ⟨E', hE'⟩ := decl2_of_decls2 hds dr (List.mem_of_find?_eq_some hfr)
    have hpe' : isPrintExt dr = false := by simp [isPrintExt, hrn]
    have hnl' : (hasPrint p && "rodata" == "printL") = false := by simp
    simp only [decl2, hpe', hrn, hnl', hs, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at hE'
    have hmr : ("rodata" == "main") = false := by decide
    simp only [hmr, Bool.false_eq_true, ↓reduceIte] at hE'
    unfold setup2 at hE'
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hE'
    obtain ⟨⟨⟨⟨⟨⟨hrt, hri⟩, hra⟩, hrr⟩, -⟩, -⟩, -⟩ := hE'
    simp [checkedOf, Scc.Frontend.entryOf, hf, ht, hi, ha, hr, checked2, entry2, hs, hfr, hrt, hri, hra, hrr,
      Except.mapError, bind, Except.bind, pure, Except.pure]

/-- **A successful `mapM`, element by element**: when each result is `F d w`
for a witness `w` with `P d w`, the results are `zipWith F` of witnesses
related pairwise. -/
theorem mapM_ok_inv {α β γ ε : Type} {f : α → Except ε β} {P : α → γ → Prop} {F : α → γ → β} :
    ∀ {ds : List α} {ys : List β}, ds.mapM f = .ok ys → (∀ d ∈ ds, ∀ y, f d = .ok y → ∃ w, P d w ∧ y = F d w) →
      ∃ ws, Pairwise2 P ds ws ∧ ys = List.zipWith F ds ws
  | [], ys, h, _ => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨[], ⟨rfl, by simp⟩, by simp [← h]⟩
  | d :: ds, ys, h, hf => by
    rw [List.mapM_cons] at h
    cases hd : f d with
    | error e => simp [hd, bind, Except.bind] at h
    | ok y =>
      cases hm : ds.mapM f with
      | error e => simp [hd, hm, bind, Except.bind] at h
      | ok ys' =>
        simp only [hd, hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨w, hw, rfl⟩ := hf d (by simp) y hd
        obtain ⟨ws, ⟨hl, hws⟩, rfl⟩ := mapM_ok_inv hm (fun x hx => hf x (by simp [hx]))
        refine ⟨w :: ws, ⟨by simp [hl], ?_⟩, by simp [← h]⟩
        intro dr hdr
        simp only [List.zip_cons_cons, List.mem_cons] at hdr
        rcases hdr with rfl | hdr
        · exact hw
        · exact hws dr hdr

/-- **Each compiled block's lowering is `func2` of its closed form**
(`accepted2_lowerC2`, `lowerDeclMarks_lowerC2`). -/
theorem lowerDeclMarks_low2 {p : Prog} (hp : Accepted2 p = true) (obj : ObjLayout) :
    ∀ d ∈ compiled2 p, ∀ fm, lowerDeclMarks p (Frontend.externs p) d obj = .ok fm →
      ∃ w, LowC2 p obj d w ∧ fm = (func2 (Names.user d.name) (paramsR d w.na) w.sc w.hp w.r, marks2 d w.na w.r) := by
  intro d hd fm hl
  obtain ⟨hdp, hc⟩ := List.mem_filter.1 hd
  have hc' : ((Frontend.externs p).any (·.1 == d.name)) = false := by simpa using hc
  obtain ⟨na, nr, sc, hq, r, hna, ha, hnr, hr, hm, hlc⟩ := accepted2_lowerC2 hp hdp hc' hl
  have := lowerDeclMarks_lowerC2 p (Frontend.externs p) obj hna ha hnr hr hm hlc
  rw [hl] at this
  cases this
  exact ⟨⟨na, sc, hq, r⟩, ⟨hna, hm, hlc⟩, rfl⟩

/-- **A successful `lowerWithMarks` of an `Accepted2` program**: the runtime
functions, then `funcs2`; the traces `marksAll2`. -/
theorem lowerWithMarks_accepted2_ok (cfg : Config) {p : Prog} (hp : Accepted2 p = true)
    {x : IR.Program × List (Sym × Array (Node × Point))}
    (h : lowerWithMarks cfg (checked2 p) = .ok x) :
    ∃ ws rt, Pairwise2 (LowC2 p cfg.layout.obj) (compiled2 p) ws ∧
      rtFuncs cfg.arch cfg.layout (entry2 p) (setupWords2 p) = .ok rt ∧
      x = (progOf cfg.layout rt (funcs2 p ws), marksAll2 p ws) := by
  unfold lowerWithMarks at h
  simp only [checked2, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i hh
  split at h
  · cases h
  rename_i um hum
  have hum' : (compiled2 p).mapM (fun d => lowerDeclMarks p (Frontend.externs p) d cfg.layout.obj) = .ok um := hum
  obtain ⟨ws, hws, rfl⟩ := mapM_ok_inv hum' (lowerDeclMarks_low2 hp cfg.layout.obj)
  rw [spawned_accepted2 hp] at h
  simp only [List.eraseDups_nil, List.mapM_nil, List.isEmpty_nil, Bool.not_true, Bool.and_false, pure,
    Except.pure] at h
  unfold rtFuncs
  by_cases hs : (setupOf p).isSome = true
  · have harg : (entry2 p).arg = .setupTid := by simp [entry2, hs]
    rw [harg] at h
    cases hr : p.find? (·.name == "rodata") with
    | none => simp [hr, throw, throwThe] at h
    | some dr =>
      cases hn : Obj.valWords dr.retTy with
      | none => simp [hr, hn, throw, throwThe] at h
      | some n =>
        simp only [hr, hn] at h
        split at h
        · cases h
        rename_i v hv
        cases h
        have hsw : setupWords2 p = n := by simp [setupWords2, hs, hr, hn]
        refine ⟨ws, v, hws, by rw [hsw]; exact hv, ?_⟩
        simp [progOf, funcs2, marksAll2, List.map_zipWith, func2]
  · have harg : (entry2 p).arg = .unit := by simp [entry2, hs]
    have hsw : setupWords2 p = 0 := by simp [setupWords2, hs]
    rw [harg] at h
    simp only at h
    repeat' (split at h)
    all_goals try cases h
    rename_i _ v hv
    refine ⟨ws, v, hws, by rw [hsw]; exact hv, ?_⟩
    simp [progOf, funcs2, marksAll2, List.map_zipWith, func2]

/-- **The lowering `lowerAll` starts from, on an `Accepted2` program**, when
it succeeds: the checked program `checked2 p`, the runtime functions, then
`func2` of each compiled code block (`funcs2`), each from its closed form
`lowerC2`; the traces `marksAll2`. -/
theorem lowerIR_accepted2 (cfg : Config) {p : Prog} (hp : Accepted2 p = true)
    {l : Lowered} (hl : lowerIR cfg p = .ok l) :
    ∃ ws rt, Pairwise2 (LowC2 p cfg.layout.obj) (compiled2 p) ws ∧
      rtFuncs cfg.arch cfg.layout (entry2 p) (setupWords2 p) = .ok rt ∧ l.checked = checked2 p ∧
      l.ir = progOf cfg.layout rt (funcs2 p ws) ∧ l.marks = marksAll2 p ws := by
  unfold lowerIR at hl
  rw [checkedOf_accepted2 hp] at hl
  simp only [bind, Except.bind] at hl
  cases hb : stackBudget cfg (checked2 p) with
  | error e => rw [hb] at hl; cases hl
  | ok b =>
    rw [hb] at hl
    cases hw : lowerWithMarks cfg (checked2 p) with
    | error e => simp only [hw] at hl; cases hl
    | ok x =>
      obtain ⟨ws, rt, hws, hrt, rfl⟩ := lowerWithMarks_accepted2_ok cfg hp hw
      simp only [hw, pure, Except.pure, Except.ok.injEq] at hl
      subst hl
      exact ⟨ws, rt, hws, hrt, rfl, rfl, rfl⟩

/-- **Compiled block `i`'s function is at index `rt.length + i`** of the
program's functions: `func2` of its lowering data `ws[i]`. -/
theorem mem_progOf_funcs2 (lay : Layout) (rt : List Func) {p : Prog} {ws : List Low2} {P : Decl → Low2 → Prop}
    (h : Pairwise2 P (compiled2 p) ws) (i : Nat) (hi : i < (compiled2 p).length) :
    (func2 (Names.user (compiled2 p)[i].name) (paramsR (compiled2 p)[i] (ws[i]'(h.1 ▸ hi)).na)
        (ws[i]'(h.1 ▸ hi)).sc (ws[i]'(h.1 ▸ hi)).hp (ws[i]'(h.1 ▸ hi)).r, rt.length + i) ∈
      (progOf lay rt (funcs2 p ws)).funcs.zipIdx := by
  have hl : i < (funcs2 p ws).length := by simp [funcs2, h.1, hi]
  have := mem_progOf_zipIdx lay rt (funcs2 p ws) i hl
  simpa [funcs2] using this

end Spike.Lib.LowerNode
