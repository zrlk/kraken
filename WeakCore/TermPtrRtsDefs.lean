import WeakCore.TermTyped
import WeakCore.TermCut

/-!
# TermPtrRtsDefs: the definitions of `TermPtrRts` read by `SysInvN`

Split out of `TermPtrRts` so that `TermMainDefs` can import them (the `TermOverCrDefs` pattern):
`tminOf`/`tminG`, `pubWords`, (M)+(R) and the clause `PtrRtsG`; and `TermPtrStab.PromInCut`.
-/

namespace TermPtrRts
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermCut
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The store typing plant edges are read against (the global `Eg.sto` in the clause; any
superset of the thread's typing in the E-parametric lemmas). -/
abbrev Sto := AllocLabel → Option Cell

/-- A plant edge: message `m` sits at a noOwn, rgnFree cell of `sto` and names label `a`. -/
def PlantEdge (sto : Sto) (m : Msg) (a : AllocLabel) : Prop :=
  (∃ ca, sto m.loc.label = some ca ∧ Ty.noOwnIn [] ca.ty = true ∧ rgnFree ca.ty = true) ∧
  ∃ (a' : Address) (g : Nat), m.val = .loc a' g ∧ a'.label = a

/-- The plant-edge test on promise index `t` (classical). -/
noncomputable def edgeB (sto : Sto) (s : St) (a : AllocLabel) (t : Ts) : Bool :=
  @decide (∃ m, s.mem[t]? = some m ∧ PlantEdge sto m a) (Classical.propDecidable _)

theorem edgeB_iff {sto : Sto} {s : St} {a : AllocLabel} {t : Ts} :
    edgeB sto s a t = true ↔ ∃ m, s.mem[t]? = some m ∧ PlantEdge sto m a := by
  unfold edgeB
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-- K-0: the least outstanding promise of `s` that is a plant edge to `a`. -/
noncomputable def tminOf (sto : Sto) (s : St) (a : AllocLabel) : Option Ts :=
  (s.promises.filter (edgeB sto s a)).min?

/-- The global form, for the `tm` parameter (no ghost): edges read against the global
store typing `Eg.sto` (so a cell joining a cut adds no edge). -/
noncomputable def tminG (Eg : GEnv) (c : Cfg) (j : Nat) (a : AllocLabel) : Option Ts :=
  match c.ths[j]? with
  | some th => tminOf Eg.sto (stOf c.mem c.pairs th) a
  | none => none

theorem tminOf_spec {sto : Sto} {s : St} {a : AllocLabel} {t : Ts} (h : tminOf sto s a = some t) :
    t ∈ s.promises ∧ ∃ m, s.mem[t]? = some m ∧ PlantEdge sto m a := by
  have hm := List.min?_mem h
  rw [List.mem_filter] at hm
  exact ⟨hm.1, edgeB_iff.1 hm.2⟩

theorem tminOf_min {sto : Sto} {s : St} {a : AllocLabel} {t u : Ts} {m : Msg} (h : tminOf sto s a = some t)
    (hu : u ∈ s.promises) (hm : s.mem[u]? = some m) (he : PlantEdge sto m a) : t ≤ u :=
  (List.le_min?_iff h).1 (Nat.le_refl t) u (List.mem_filter.2 ⟨hu, edgeB_iff.2 ⟨m, hm, he⟩⟩)

theorem tminOf_none {sto : Sto} {s : St} {a : AllocLabel} (h : tminOf sto s a = none) :
    ∀ u ∈ s.promises, ∀ m, s.mem[u]? = some m → ¬ PlantEdge sto m a := by
  intro u hu m hm he
  have h0 := List.min?_eq_none_iff.1 h
  have : u ∈ s.promises.filter (edgeB sto s a) := List.mem_filter.2 ⟨hu, edgeB_iff.2 ⟨m, hm, he⟩⟩
  rw [h0] at this; cases this

theorem edgeB_congr {sto sto2 : Sto} {s s2 : St} {a : AllocLabel} {u : Ts} (hs : sto = sto2)
    (hm : s.mem[u]? = s2.mem[u]?) : edgeB sto s a u = edgeB sto2 s2 a u := by
  apply Bool.eq_iff_iff.2
  rw [edgeB_iff, edgeB_iff, hm, hs]

theorem tminOf_congr {sto sto2 : Sto} {s s2 : St} {a : AllocLabel} (hs : sto = sto2)
    (hp : s.promises = s2.promises) (hm : ∀ u ∈ s.promises, s.mem[u]? = s2.mem[u]?) :
    tminOf sto s a = tminOf sto2 s2 a := by
  unfold tminOf
  rw [← hp]
  congr 1
  exact List.filter_congr fun u hu => edgeB_congr hs (hm u hu)

theorem tminG_eq {Eg : GEnv} {c : Cfg} {j : Nat} {a : AllocLabel} {th : TTh} (hth : c.ths[j]? = some th) :
    tminG Eg c j a = tminOf Eg.sto (stOf c.mem c.pairs th) a := by
  unfold tminG
  rw [hth]

/-! ## Pub-position words (`cnt`) -/

/-- Under a shallow-pub type every word counts. -/
theorem pubWords_of_sNo {t : Ty} (h : sNo t = true) (ws : List Word) : pubWords t ws = ws := by
  cases t
  all_goals first
    | (simp only [pubWords, h, ite_true]; done)
    | (rw [pubWords.eq_def]; simp only [h, ite_true])

/-- A word names `a`. -/
def Names (a : AllocLabel) (w : Word) : Prop := ∃ (a' : Address) (g : Nat), w.val = .loc a' g ∧ a'.label = a

/-- (R) for one environment: every pub-position word naming `a` has rts ≥ `t`. -/
def EnvRts (t : Ts) (a : AllocLabel) (env : Env) : Prop :=
  ∀ x rt ws, (x, rt, ws) ∈ env → ∀ w ∈ pubWords rt ws, Names a w → t ≤ w.rts

def StackRts (t : Ts) (a : AllocLabel) (st : List Frame) : Prop :=
  ∀ f ∈ st, EnvRts t a f.env

/-- (R), thread-level: the frame env and the stack (the registers are scratch, `mth`). -/
def ThRts (t : Ts) (a : AllocLabel) (th : TTh) : Prop := EnvRts t a th.env ∧ StackRts t a th.stack

/-- (M), edge form: every non-promise message at a noOwn, rgnFree cell of `sto` naming `a` has
index ≥ `t`.  (The OwnPos form implies it: `MemRts_of_own`.) -/
def MemRts (sto : Sto) (t : Ts) (a : AllocLabel) (mem : Memory) (P : List Ts) : Prop :=
  ∀ u m, mem[u]? = some m → PlantEdge sto m a → u ∉ P → t ≤ u

/-- **K-1**: (M)+(R) for owner thread state `s`, frame `th`, edges read against `sto`. -/
def PtrRtsE (sto : Sto) (s : St) (th : TTh) (a : AllocLabel) : Prop :=
  ∀ t, tminOf sto s a = some t → MemRts sto t a s.mem s.promises ∧ ThRts t a th

/-- The SysInvN clause (`ptrRts : k.storeDepRts = true → PtrRtsG Eg Tot HP c`). Edges are read
against the global `Eg.sto`; (R) is the owner thread's only (frame + stack: other threads' words reach
the owner through memory, which (M) covers); (M) is against the owner's own promises.
The gate is the owner's own key (frame or private holding): `publish` consumes it, so a published
cell is out of scope (the shared holding is own-free at a key-held label, `ownNet_one`). -/
def PtrRtsG (Eg : GEnv) (Tot HP : Nat → Res) (c : Cfg) : Prop :=
  ∀ (j : Nat) th a cl f, c.ths[j]? = some th → Eg.sto a = some cl → cl.owner = some j →
    Eg.pfr a = some f → 0 < (Tot j + HP j) (.own a) → ∀ t, tminG Eg c j a = some t →
      MemRts Eg.sto t a c.mem th.promises ∧ ThRts t a th


/-! ## The erased witness (`unpackT`): guarded substitution keeps the counted words -/

theorem sNo_substT_unit : ∀ (t : Ty) (k : Nat), sNo (Ty.substT k .unit t) = sNo t := by
  intro t
  induction t with
  | tvar i => intro k; simp only [Ty.substT]; split <;> (try split) <;> rfl
  | prod a b iha ihb => intro k; simp only [Ty.substT, sNo, iha, ihb]
  | sum a b iha ihb => intro k; simp only [Ty.substT, sNo, iha, ihb]
  | refine t ψ ih => intro k; simp only [Ty.substT, sNo, ih]
  | iall t ih => intro k; exact ih k
  | iex t ih => intro k; exact ih k
  | mu t ih => intro k; exact ih (k + 1)
  | tex κ t ih => intro k; simp only [Ty.substT, sNo]; rw [show Ty.shiftT 0 Ty.unit = Ty.unit from rfl, ih]
  | array i t ih => intro k; exact ih k
  | _ => intro k; rfl

theorem tyMentions_substT_unit : ∀ (t : Ty) (k j : Nat), j < k →
    (Ty.substT k .unit t).tyMentions j = t.tyMentions j := by
  intro t
  induction t with
  | tvar i =>
      intro k j h
      simp only [Ty.substT]
      by_cases h1 : i = k
      · subst h1; simp [Ty.tyMentions]; omega
      · by_cases h2 : i > k
        · have h3 : i - 1 ≠ j := by omega
          have h4 : i ≠ j := by omega
          simp only [beq_iff_eq, h1, ite_false, h2, ite_true, Ty.tyMentions]
          rw [beq_eq_false_iff_ne.2 h3, beq_eq_false_iff_ne.2 h4]
        · simp [h1, h2]
  | prod a b iha ihb => intro k j h; simp only [Ty.substT, Ty.tyMentions, iha k j h, ihb k j h]
  | sum a b iha ihb => intro k j h; simp only [Ty.substT, Ty.tyMentions, iha k j h, ihb k j h]
  | code a b iha ihb => intro k j h; simp only [Ty.substT, Ty.tyMentions, iha k j h, ihb k j h]
  | array i t ih => intro k j h; simp only [Ty.substT, Ty.tyMentions, ih k j h]
  | ptr μ t ih => intro k j h; simp only [Ty.substT, Ty.tyMentions, ih k j h]
  | ptrOpt μ t ih => intro k j h; simp only [Ty.substT, Ty.tyMentions, ih k j h]
  | loc μ t ih => intro k j h; simp only [Ty.substT, Ty.tyMentions, ih k j h]
  | mu t ih => intro k j h; exact ih (k + 1) (j + 1) (by omega)
  | tex κ t ih => intro k j h; exact ih (k + 1) (j + 1) (by omega)
  | iall t ih => intro k j h; exact ih k j h
  | iex t ih => intro k j h; exact ih k j h
  | refine t ψ ih => intro k j h; simp only [Ty.substT, Ty.tyMentions, ih k j h]
  | _ => intro k j h; rfl

theorem idxMentions_substT_unit : ∀ (t : Ty) (k j : Nat),
    (Ty.substT k .unit t).idxMentions j = t.idxMentions j := by
  intro t
  induction t with
  | tvar i =>
      intro k j
      simp only [Ty.substT]
      split
      · rfl
      · split <;> rfl
  | prod a b iha ihb => intro k j; simp only [Ty.substT, Ty.idxMentions, iha, ihb]
  | sum a b iha ihb => intro k j; simp only [Ty.substT, Ty.idxMentions, iha, ihb]
  | code a b iha ihb => intro k j; simp only [Ty.substT, Ty.idxMentions, iha, ihb]
  | array i t ih => intro k j; simp only [Ty.substT, Ty.idxMentions, ih]
  | ptr μ t ih => intro k j; simp only [Ty.substT, Ty.idxMentions, ih]
  | ptrOpt μ t ih => intro k j; simp only [Ty.substT, Ty.idxMentions, ih]
  | loc μ t ih => intro k j; simp only [Ty.substT, Ty.idxMentions, ih]
  | mu t ih => intro k j; exact ih (k + 1) j
  | tex κ t ih => intro k j; exact ih (k + 1) j
  | iall t ih => intro k j; exact ih k (j + 1)
  | iex t ih => intro k j; exact ih k (j + 1)
  | refine t ψ ih => intro k j; simp only [Ty.substT, Ty.idxMentions, ih]
  | _ => intro k j; rfl

theorem shiftT_unit (c : Nat) : Ty.shiftT c Ty.unit = Ty.unit := rfl
theorem shiftI_unit (c : Nat) : Ty.shiftI c Ty.unit = Ty.unit := rfl

theorem countT_substT_unit : ∀ (t : Ty) (k j : Nat), j < k →
    (Ty.substT k .unit t).countT j = t.countT j := by
  intro t
  induction t with
  | tvar i =>
      intro k j h
      simp only [Ty.countT]
      rw [← tyMentions_substT_unit (.tvar i) k j h]
      simp only [Ty.substT]
      split <;> (try split) <;> simp_all [Ty.countT, Ty.tyMentions]
  | prod a b iha ihb => intro k j h; simp only [Ty.substT, Ty.countT, iha k j h, ihb k j h]
  | refine t ψ ih => intro k j h; simp only [Ty.substT, Ty.countT, ih k j h]
  | iall t ih => intro k j h; simp only [Ty.substT, shiftI_unit, Ty.countT, ih k j h]
  | iex t ih => intro k j h; simp only [Ty.substT, shiftI_unit, Ty.countT, ih k j h]
  | tex κ t ih => intro k j h; simp only [Ty.substT, shiftT_unit, Ty.countT, ih (k + 1) (j + 1) (by omega)]
  | mu t ih =>
      intro k j h
      simp only [Ty.substT, shiftT_unit, Ty.countT, ih (k + 1) (j + 1) (by omega), ih (k + 1) 0 (by omega),
        tyMentions_substT_unit t (k + 1) (j + 1) (by omega)]
  | sum a b _ _ => intro k j h; simp only [Ty.countT]; rw [← tyMentions_substT_unit (.sum a b) k j h]; simp only [Ty.substT, Ty.countT]; rfl
  | code a b _ _ => intro k j h; simp only [Ty.countT]; rw [← tyMentions_substT_unit (.code a b) k j h]; simp only [Ty.substT, Ty.countT]; rfl
  | array i t _ => intro k j h; simp only [Ty.countT]; rw [← tyMentions_substT_unit (.array i t) k j h]; simp only [Ty.substT, Ty.countT]; rfl
  | ptr μ t _ => intro k j h; simp only [Ty.countT]; rw [← tyMentions_substT_unit (.ptr μ t) k j h]; simp only [Ty.substT, Ty.countT]; rfl
  | ptrOpt μ t _ => intro k j h; simp only [Ty.countT]; rw [← tyMentions_substT_unit (.ptrOpt μ t) k j h]; simp only [Ty.substT, Ty.countT]; rfl
  | loc μ t _ => intro k j h; simp only [Ty.countT]; rw [← tyMentions_substT_unit (.loc μ t) k j h]; simp only [Ty.substT, Ty.countT]; rfl
  | _ => intro k j h; rfl

theorem countI_substT_unit : ∀ (t : Ty) (k j : Nat),
    (Ty.substT k .unit t).countI j = t.countI j := by
  intro t
  induction t with
  | tvar i =>
      intro k j
      simp only [Ty.countI]
      rw [← idxMentions_substT_unit (.tvar i) k j]
      simp only [Ty.substT]
      split <;> (try split) <;> simp_all [Ty.countI, Ty.idxMentions]
  | prod a b iha ihb => intro k j; simp only [Ty.substT, Ty.countI, iha, ihb]
  | refine t ψ ih => intro k j; simp only [Ty.substT, Ty.countI, ih]
  | iall t ih => intro k j; simp only [Ty.substT, shiftI_unit, Ty.countI, ih]
  | iex t ih => intro k j; simp only [Ty.substT, shiftI_unit, Ty.countI, ih]
  | tex κ t ih => intro k j; simp only [Ty.substT, shiftT_unit, Ty.countI, ih]
  | mu t ih =>
      intro k j
      simp only [Ty.substT, shiftT_unit, Ty.countI, ih, idxMentions_substT_unit,
        countT_substT_unit t (k + 1) 0 (by omega)]
  | sum a b _ _ => intro k j; simp only [Ty.countI]; rw [← idxMentions_substT_unit (.sum a b) k j]; simp only [Ty.substT, Ty.countI]; rfl
  | code a b _ _ => intro k j; simp only [Ty.countI]; rw [← idxMentions_substT_unit (.code a b) k j]; simp only [Ty.substT, Ty.countI]; rfl
  | array i t _ => intro k j; simp only [Ty.countI]; rw [← idxMentions_substT_unit (.array i t) k j]; simp only [Ty.substT, Ty.countI]; rfl
  | ptr μ t _ => intro k j; simp only [Ty.countI]; rw [← idxMentions_substT_unit (.ptr μ t) k j]; simp only [Ty.substT, Ty.countI]; rfl
  | ptrOpt μ t _ => intro k j; simp only [Ty.countI]; rw [← idxMentions_substT_unit (.ptrOpt μ t) k j]; simp only [Ty.substT, Ty.countI]; rfl
  | loc μ t _ => intro k j; simp only [Ty.countI]; rw [← idxMentions_substT_unit (.loc μ t) k j]; simp only [Ty.substT, Ty.countI]; rfl
  | _ => intro k j; rfl

/-- `info` at an all-unknown context does not see a guarded variable's substitution. -/
theorem info_substT_unit : ∀ (t : Ty) (k : Nat) (ρ : Ctx), (∀ i, ρ i = none) → t.guardT k = true →
    info ρ (Ty.substT k .unit t) = info ρ t := by
  intro t
  induction t with
  | tvar i =>
      intro k ρ hρ hg
      have hk : i ≠ k := by simpa [Ty.guardT] using hg
      simp only [Ty.substT, beq_iff_eq, hk, ite_false]
      split <;> simp only [info, hρ]
  | prod a b iha ihb =>
      intro k ρ hρ hg
      simp only [Ty.guardT, Bool.and_eq_true] at hg
      simp only [Ty.substT, info, iha k ρ hρ hg.1, ihb k ρ hρ hg.2]
  | sum a b iha ihb =>
      intro k ρ hρ hg
      simp only [Ty.guardT, Bool.and_eq_true] at hg
      simp only [Ty.substT, info, iha k ρ hρ hg.1, ihb k ρ hρ hg.2]
  | refine t ψ ih => intro k ρ hρ hg; exact ih k ρ hρ hg
  | iall t ih =>
      intro k ρ hρ hg
      simp only [Ty.substT, shiftI_unit, info]
      rw [ih k ρ.shiftI (fun i => by simp [Ctx.shiftI, hρ]) hg]
  | iex t ih =>
      intro k ρ hρ hg
      simp only [Ty.substT, shiftI_unit, info]
      rw [ih k ρ.shiftI (fun i => by simp [Ctx.shiftI, hρ]) hg]
  | mu t ih =>
      intro k ρ hρ hg
      simp only [Ty.substT, shiftT_unit, info]
      exact ih (k + 1) _ (fun i => by cases i <;> simp [Ctx.cons, hρ]) hg
  | tex κ t ih =>
      intro k ρ hρ hg
      simp only [Ty.substT, shiftT_unit, info]
      exact ih (k + 1) _ (fun i => by cases i <;> simp [Ctx.cons, hρ]) hg
  | _ => intro k ρ hρ hg; rfl

theorem lnorm_substT_unit : ∀ (t : Ty) (k : Nat), t.guardT k = true → lnorm (Ty.substT k .unit t) = lnorm t := by
  intro t
  induction t with
  | tvar i =>
      intro k hg
      have hk : i ≠ k := by simpa [Ty.guardT] using hg
      simp only [Ty.substT, beq_iff_eq, hk, ite_false]
      split <;> rfl
  | prod a b iha ihb =>
      intro k hg
      simp only [Ty.guardT, Bool.and_eq_true] at hg
      simp only [Ty.substT, lnorm, iha k hg.1, ihb k hg.2]
  | sum a b iha ihb =>
      intro k hg
      simp only [Ty.guardT, Bool.and_eq_true] at hg
      simp only [Ty.substT, lnorm, iha k hg.1, ihb k hg.2]
  | refine t ψ ih => intro k hg; exact ih k hg
  | iall t ih => intro k hg; simp only [Ty.substT, shiftI_unit, lnorm, ih k hg]
  | iex t ih => intro k hg; simp only [Ty.substT, shiftI_unit, lnorm, ih k hg]
  | mu t ih => intro k hg; simp only [Ty.substT, shiftT_unit, lnorm, ih (k + 1) hg]
  | tex κ t ih => intro k hg; simp only [Ty.substT, shiftT_unit, lnorm, ih (k + 1) hg]
  | _ => intro k hg; rfl

theorem armsOf_len_substT_unit : ∀ (t : Ty) (k : Nat),
    (armsOf (Ty.substT k .unit t)).length = (armsOf t).length := by
  intro t
  induction t with
  | tvar i => intro k; simp only [Ty.substT]; split <;> (try split) <;> rfl
  | sum a b iha ihb => intro k; simp only [Ty.substT, armsOf, List.length_append, iha, ihb]
  | refine t ψ ih => intro k; exact ih k
  | iall t ih => intro k; exact ih k
  | iex t ih => intro k; exact ih k
  | mu t ih => intro k; exact ih (k + 1)
  | tex κ t ih => intro k; exact ih (k + 1)
  | _ => intro k; rfl

theorem rawWords_substT_unit {t : Ty} {k : Nat} (hg : t.guardT k = true) :
    (Ty.substT k .unit t).rawWords = t.rawWords := by
  simp only [Ty.rawWords, Ty.width, info_substT_unit t k Ty.top (fun _ => rfl) hg]

theorem tier_substT_unit {t : Ty} {k : Nat} (hg : t.guardT k = true) :
    (Ty.substT k .unit t).tier = t.tier := by
  simp only [Ty.tier, info_substT_unit t k Ty.top (fun _ => rfl) hg]

theorem accs_substT_unit : ∀ (t : Ty) (k : Nat), t.guardT k = true → accs (Ty.substT k .unit t) = accs t := by
  intro t
  induction t with
  | tvar i =>
      intro k hg
      have hk : i ≠ k := by simpa [Ty.guardT] using hg
      simp only [Ty.substT, beq_iff_eq, hk, ite_false]
      split <;> rfl
  | prod a b iha ihb =>
      intro k hg
      simp only [Ty.guardT, Bool.and_eq_true] at hg
      simp only [Ty.substT, accs, iha k hg.1, ihb k hg.2]
  | sum a b _ _ =>
      intro k hg
      have e := tier_substT_unit (t := .sum a b) hg
      simp only [Ty.substT] at e ⊢
      simp only [accs, e]
  | refine t ψ ih => intro k hg; exact ih k hg
  | iall t ih => intro k hg; exact ih k hg
  | mu t ih => intro k hg; exact ih (k + 1) hg
  | iex t ih =>
      intro k hg
      have e := rawWords_substT_unit (t := .iex t) hg
      simp only [Ty.substT, shiftI_unit] at e ⊢
      simp only [accs, e, countI_substT_unit, ih k hg]
  | tex κ t ih =>
      intro k hg
      have e := rawWords_substT_unit (t := .tex κ t) hg
      simp only [Ty.substT, shiftT_unit] at e ⊢
      simp only [accs, e, countT_substT_unit t (k + 1) 0 (by omega), ih (k + 1) hg]
  | _ => intro k hg; rfl

theorem wc_substT_unit {t : Ty} {k : Nat} (hg : t.guardT k = true) : wc (Ty.substT k .unit t) = wc t := by
  simp only [wc, accs_substT_unit t k hg]

/-- **Unpack/pack** (24e, `unpackT`): replacing a guarded type variable by the erased witness `unit`
changes no counted word — the variable occurs only under references, which `cnt` never enters. -/
theorem pubWords_substT_unit : ∀ (t : Ty) (k : Nat), t.guardT k = true →
    (∀ ws, pubWords (Ty.substT k .unit t) ws = pubWords t ws) ∧
    (∀ j p, pubArm (Ty.substT k .unit t) j p = pubArm t j p) := by
  intro t
  induction t with
  | tvar i =>
      intro k hg
      have hk : i ≠ k := by simpa [Ty.guardT] using hg
      simp only [Ty.substT, beq_iff_eq, hk, ite_false]
      split <;> exact ⟨fun ws => by simp [pubWords, sNo], fun j p => by simp [pubArm, pubWords, sNo]⟩
  | prod a b iha ihb =>
      intro k hg
      have hs := sNo_substT_unit (.prod a b) k
      simp only [Ty.guardT, Bool.and_eq_true] at hg
      simp only [Ty.substT] at hs ⊢
      have hw := wc_substT_unit hg.1
      have h1 : ∀ ws, pubWords (.prod (Ty.substT k .unit a) (Ty.substT k .unit b)) ws = pubWords (.prod a b) ws := by
        intro ws
        simp only [pubWords, hs, hw, (iha k hg.1).1, (ihb k hg.2).1]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      intro k hg
      have hs := sNo_substT_unit (.sum a b) k
      have ht := tier_substT_unit (t := .sum a b) hg
      have hl := lnorm_substT_unit (.sum a b) k hg
      simp only [Ty.guardT, Bool.and_eq_true] at hg
      simp only [Ty.substT] at hs ht hl ⊢
      have hal := armsOf_len_substT_unit a k
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · simp only [pubWords, hs, ht, hl, hal, (iha k hg.1).2, (ihb k hg.2).2]
      · simp only [pubArm, hal, (iha k hg.1).2, (ihb k hg.2).2]
  | refine t ψ ih =>
      intro k hg
      have hs := sNo_substT_unit (.refine t ψ) k
      simp only [Ty.guardT] at hg
      simp only [Ty.substT] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih k hg).1],
        fun j p => by simp only [pubArm, (ih k hg).2]⟩
  | iall t ih =>
      intro k hg
      have hs := sNo_substT_unit (.iall t) k
      simp only [Ty.guardT] at hg
      simp only [Ty.substT, shiftI_unit] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih k hg).1],
        fun j p => by simp only [pubArm, (ih k hg).2]⟩
  | iex t ih =>
      intro k hg
      have hs := sNo_substT_unit (.iex t) k
      simp only [Ty.guardT] at hg
      simp only [Ty.substT, shiftI_unit] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih k hg).1],
        fun j p => by simp only [pubArm, (ih k hg).2]⟩
  | mu t ih =>
      intro k hg
      have hs := sNo_substT_unit (.mu t) k
      simp only [Ty.guardT] at hg
      simp only [Ty.substT, shiftT_unit] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih (k + 1) hg).1],
        fun j p => by simp only [pubArm, (ih (k + 1) hg).2]⟩
  | tex κ t ih =>
      intro k hg
      have hs := sNo_substT_unit (.tex κ t) k
      simp only [Ty.guardT] at hg
      simp only [Ty.substT, shiftT_unit] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih (k + 1) hg).1],
        fun j p => by simp only [pubArm, (ih (k + 1) hg).2]⟩
  | array i e ih =>
      intro k hg
      have hs := sNo_substT_unit (.array i e) k
      simp only [Ty.guardT] at hg
      simp only [Ty.substT] at hs ⊢
      have h1 : ∀ ws, pubWords (.array i (Ty.substT k .unit e)) ws = pubWords (.array i e) ws := by
        intro ws
        rw [pubWords.eq_def, pubWords.eq_def]
        simp only [hs]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | ptr μ u _ => intro k hg; exact ⟨fun ws => by simp only [Ty.substT, pubWords, sNo]; rfl, fun j p => by simp only [Ty.substT, pubArm, pubWords, sNo]; rfl⟩
  | ptrOpt μ u _ => intro k hg; exact ⟨fun ws => by simp only [Ty.substT, pubWords, sNo]; rfl, fun j p => by simp only [Ty.substT, pubArm, pubWords, sNo]; rfl⟩
  | loc μ u _ => intro k hg; exact ⟨fun ws => by simp only [Ty.substT, pubWords, sNo]; rfl, fun j p => by simp only [Ty.substT, pubArm, pubWords, sNo]; rfl⟩
  | code a b _ _ => intro k hg; exact ⟨fun ws => by simp only [Ty.substT, pubWords, sNo], fun j p => by simp only [Ty.substT, pubArm, pubWords, sNo]⟩
  | _ => intro k hg; exact ⟨fun ws => rfl, fun j p => rfl⟩

/-- `unpackT`'s runtime step (TermRun: `(x, substT 0 unit b, ws)` from `(a, tex κ b, ws)`): the
same counted words, for any kind `κ` (the `tex` gate is gone). -/
theorem pubWords_unpackT {κ : Kind} {b : Ty} (hg : b.guardT 0 = true) (ws : List Word) :
    pubWords (Ty.substT 0 .unit b) ws = pubWords (.tex κ b) ws := by
  rw [(pubWords_substT_unit b 0 hg).1 ws]
  by_cases h : sNo (.tex κ b) = true
  · have hb : sNo b = true := by simp only [sNo, Bool.and_eq_true] at h; exact h.2
    rw [pubWords_of_sNo h, pubWords_of_sNo hb]
  · simp only [pubWords, h, Bool.false_eq_true, ite_false]


/-! ## (I2, staging) Words name only allocated labels -/

/-- (EnvPub) Every counted word of `env` naming a label names a published or planted cell
(`pfr` some) or a box: a counted word is a `pub`/`opq` reference, which `VR` reads through `η.pfr`, or
a boxed sum, through `η.box` (`labsIn_pubVR`); a dead binding was typed when bound. -/
def EnvLbl (Eg : GEnv) (env : Env) : Prop :=
  ∀ x rt ws, (x, rt, ws) ∈ env → ∀ w ∈ pubWords rt ws, ∀ l, Names l w → Eg.pfr l ≠ none ∨ Eg.box l ≠ none

/-- **LblSto** (staging): `EnvLbl` for every thread's frame and stack environments.
Memory is not included (`MemOKP` types non-promise messages; promise values are exempt). -/
def LblSto (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ (i : Nat) th, c.ths[i]? = some th → EnvLbl Eg th.env ∧ ∀ f ∈ th.stack, EnvLbl Eg f.env

/-- **GateTmin** (staging part (b)): at a gated cell (the owner's, key held) that is
planted or published, `tminG` is some. -/
def GateTmin (Eg : GEnv) (Tot HP : Nat → Res) (c : Cfg) : Prop :=
  ∀ (j : Nat) a cl f, Eg.sto a = some cl → cl.owner = some j → Eg.pfr a = some f →
    0 < (Tot j + HP j) (.own a) → tminG Eg c j a ≠ none

/-! ## (M), counted-slot form (option (a′)) -/

/-- The counted positions of a value `ws` of runtime type `S`: `pubWords` by position (each word's
`rts` replaced by its index plus one; `pubWords` reads only `val`).  The words `pubWords` synthesises
(a niche `Ptr?` arm's `cst .null`, `rts = 0`) are dropped. -/
def cntIdx (S : Ty) (ws : List Word) : List Nat :=
  (pubWords S (ws.mapIdx fun i w => { w with rts := i + 1 })).filterMap fun w =>
    if w.rts = 0 then none else some (w.rts - 1)

/-- Word `o` of a cell of type `T`, holding `w`, is at a counted position of a segment value of the
right shape holding `w` there. -/
def CntOK (T : Ty) (o : Nat) (w : Word) : Prop :=
  ∃ b S ws o', SegOf T b S ∧ ShapeC S ws ∧ ws[o']? = some w ∧ b + o' = o ∧ o' ∈ cntIdx S ws

/-- The second word `w1` of a pair store (first word `w0` at `o`) is at a counted position of a
segment value of the right shape holding both. -/
def CntPairOK (T : Ty) (o : Nat) (w0 w1 : Word) : Prop :=
  ∃ b S ws o', SegOf T b S ∧ ShapeC S ws ∧ ws[o']? = some w0 ∧ ws[o' + 1]? = some w1 ∧ b + o' = o ∧
    o' + 1 ∈ cntIdx S ws

/-- The access unit holding word `i` of a layout, and `i`'s place in it. -/
def UnitAt : List Acc → Nat → Option (Acc × Nat)
  | [], _ => none
  | u :: us, i => if i < u.size then some (u, i) else UnitAt us (i - u.size)

/-- Word `o` of a cell of type `T` is not the second word of a two-word unit (granule) of a
segment. -/
def NotSnd (T : Ty) (o : Nat) : Prop :=
  ∀ b S us oo u d, SegOf T b S → accs S = some us → b + oo = o → UnitAt us oo = some (u, d) → d = 0

/-- **(M), counted-slot form**: every non-promise message naming `a` at a counted slot of a cell of
`sto` has index `≥ t`.  A message not at a granule's second word is read on its own (`CntOK`,
determined by the word: `TermCntLoc.cntOK_typed`); a pair store's second half together with its
first (`CntPairOK`). -/
def MemRtsC (sto : Sto) (t : Ts) (a : AllocLabel) (mem : Memory) (pairs P : List Ts) : Prop :=
  ∀ u m cl, mem[u]? = some m → u ∉ P → sto m.loc.label = some cl → Names a (mw m) →
    ((NotSnd cl.ty m.loc.offset ∧ CntOK cl.ty m.loc.offset (mw m)) ∨
      ∃ v m0, v + 1 = u ∧ v ∈ pairs ∧ mem[v]? = some m0 ∧ m0.loc.label = m.loc.label ∧
        CntPairOK cl.ty m0.loc.offset (mw m0) (mw m)) → t ≤ u

/-- The global form, gated as `PtrRtsG`: edges and counted slots read against `Eg.sto`. -/
def MemRtsCG (Eg : GEnv) (Tot HP : Nat → Res) (c : Cfg) : Prop :=
  ∀ (j : Nat) th a cl f, c.ths[j]? = some th → Eg.sto a = some cl → cl.owner = some j →
    Eg.pfr a = some f → 0 < (Tot j + HP j) (.own a) → ∀ t, tminG Eg c j a = some t →
      MemRtsC Eg.sto t a c.mem c.pairs th.promises

/-- **Granules are written whole** (`granW`): a pair store's two messages are at consecutive words;
once a pair is written at a word, every later message there is a pair store's first; and a pair
store at a cell of `sto` starts a two-word unit of the cell (`TwoAtT`).  (v3c, clause 4) A message at
the second word of a two-word unit of a cell of `sto` is a pair store's second half or holds no
pointer. -/
def GranuleW (sto : Sto) (mem : Memory) (pairs : List Ts) : Prop :=
  (∀ q ∈ pairs, ∃ m0 m1, mem[q]? = some m0 ∧ mem[q + 1]? = some m1 ∧ m1.loc = m0.loc.next) ∧
  (∀ q ∈ pairs, ∀ (v : Nat) (m0 mv : Msg), mem[q]? = some m0 → mem[v]? = some mv → mv.loc = m0.loc → q < v →
    v ∈ pairs) ∧
  (∀ q ∈ pairs, ∀ (m0 : Msg) (cl : Cell), mem[q]? = some m0 → sto m0.loc.label = some cl →
    TwoAtT cl.ty m0.loc.offset) ∧
  (∀ (v : Nat) (mv : Msg) (cl : Cell) (o : Nat), mem[v]? = some mv → sto mv.loc.label = some cl →
    mv.loc.offset = o + 1 → TwoAtT cl.ty o → (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ pairs, v = q + 1)

/-- The staging package: `PtrRtsG` with `LblSto`, `GateTmin` and `MemRtsCG` bundled (not in
`SysInvN`). -/
def PtrRtsGL (Eg : GEnv) (Tot HP : Nat → Res) (c : Cfg) : Prop :=
  PtrRtsG Eg Tot HP c ∧ LblSto Eg c ∧ GateTmin Eg Tot HP c ∧ MemRtsCG Eg Tot HP c

/-- **BoxPlantSep** (the text). -/
def BoxPlantSep (Eg : GEnv) (Tot HP : Nat → Res) (c : Cfg) : Prop :=
  ∀ l B, Eg.box l = some B → ∀ o w, B.pay[o]? = some w → ∀ j th a cl f t, c.ths[j]? = some th →
    Eg.sto a = some cl → cl.owner = some j → Eg.pfr a = some f → 0 < (Tot j + HP j) (.own a) →
    tminG Eg c j a = some t → Names a w →
    w.view < f ∨ ∀ u m, c.mem[u]? = some m → m.loc = ⟨l, o + 1⟩ → m.val = w.val → t ≤ u

/-- **BoxPlantSep, pre-state** (the text; staged, SysInvN part to): a payload word of a
box naming `a` is below `a`'s frontier in view, or every message carrying it at its box slot has index
`≥ t`. -/
def BoxSep (E : TEnv) (t : Ts) (a : AllocLabel) (mem : Memory) : Prop :=
  ∀ l B, E.box l = some B → ∀ o w, B.pay[o]? = some w → Names a w → ∀ f, E.pfr a = some f →
    w.view < f ∨ ∀ u m, mem[u]? = some m → m.loc = ⟨l, o + 1⟩ → m.val = w.val → t ≤ u

end TermPtrRts

namespace TermPtrStab
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped TermCut
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- Every outstanding promise of `j` at a cell of Σ lies in `j`'s cut (own or shared). -/
def PromInCut (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ (j : Nat) (th : TTh) (t : Ts) (m : Msg), c.ths[j]? = some th → t ∈ th.promises → c.mem[t]? = some m →
    ∀ cm, Eg.sto m.loc.label = some cm → cm.owner = some j ∨ Eg.Shared m.loc.label

end TermPtrStab
