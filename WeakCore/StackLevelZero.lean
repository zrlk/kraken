import WeakCore.StackInduction
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! Level-0 wiring of F4: the identity level relates the caller's W env `η` to `flat η`, and `f4` at `Lv.id0`
gives the (local-mirror) `ContB` conclusion. -/

theorem map_rl_idf {f : WeakMem.AllocLabel → WeakMem.AllocLabel} (hf : ∀ m, f m = m) :
    ∀ (ws : List Word), ws.map (rl f) = ws
  | [] => rfl
  | w :: ws => by
    simp only [List.map_cons, map_rl_idf hf ws]
    congr 1
    unfold rl
    cases w with
    | mk v => cases v <;> simp [rlv, hf]

/-- The anchor is blank on the plan tail (the supply bound at the plan's parameters). -/
def TailBlank (P : Plan) (η : TEnv) : Prop :=
  ∀ m, P.Tail P.N m → η.sto m = none ∧ η.box m = none ∧ η.ini m = 0 ∧ η.rini m = 0 ∧ η.pfr m = none ∧ ¬ η.seen m

theorem relW_id0 {P : Plan} {η : TEnv} (hc : Coh η) (hbl : TailBlank P η) :
    RelW (Lv.id0 P) η (FlatAnchor.flat η) := by
  have hO : ∀ m, ¬ (Lv.id0 P).Old m := fun m h => by rcases h with h | h <;> exact h
  refine { coh := hc,
           fsto := fun m _ ht => by obtain ⟨h, -⟩ := hbl m ht; exact h,
           fbox := fun m _ ht => by obtain ⟨-, h, -⟩ := hbl m ht; exact h,
           fini := fun m _ ht => by obtain ⟨-, -, h, -⟩ := hbl m ht; exact h,
           frini := fun m _ ht => by obtain ⟨-, -, -, h, -⟩ := hbl m ht; exact h,
           fpfr := fun m _ ht => by obtain ⟨-, -, -, -, h, -⟩ := hbl m ht; exact h,
           fseen := fun m _ ht => by obtain ⟨-, -, -, -, -, h⟩ := hbl m ht; exact h,
           sto := fun m c _ h => h, ini := fun m _ => Nat.le_refl _, rini := fun m _ => Nat.le_refl _,
           pfr := fun m q _ h => h, seen := fun m _ h => h,
           box := fun m B _ h => ⟨B, h, ?_⟩, pay := fun x B _ w _ a g _ => hO _,
           rid := Nat.le_refl _, wit := rfl, prog := rfl, tid := rfl,
           vsto := fun m h => h.elim, ocl := ?_, oinil := ?_, orinil := ?_, opfrl := ?_, opfrc := ?_,
           oini := ?_, orini := ?_, opfr := ?_, oseen := ?_, obox := ?_, opay := ?_ }
  · cases B; simp only [Lv.id0, map_rl_idf (fun _ => rfl)]
  all_goals (intro m; first | (intro _ ho; exact absurd ho (hO m)) | (intro ho; exact absurd ho (hO m)))

/-- **Level 0** (F4 at the identity level). Mirror form: the conclusion is the supply mirror; it unfolds to
`ContB`; RsSup at level 0 comes from the supply bound (`planAt`). -/
theorem contB_f4 {p : Prog} {P : Plan} {Sup : TEnv → Prop}
    (hSup : ∀ η, Sup η → ∃ b, FreshSup P b η)
    {stack : List Frame} {σs : List Ty} {E : TEnv}
    (hM : 3 * (stack.length + 1) ≤ P.M) (hStk : StkLt P stack) (hbl : TailBlank P E) :
    ∀ (ρ : Nat → Nat) (η : TEnv) (cx : Cx) (Rs : Res), CE η = E → EnvOK p η → RsSup P Rs →
      RetOKR ρ η σs cx.ret (ResumeR p stack Rs) →
      RetOKRBs Sup glb gnum gi ρ (FlatAnchor.flat η) σs cx.ret (ResumeRBs Sup glb gnum gi p stack Rs) := by
  intro ρ η cx Rs hCE hE hRs hK
  subst hCE
  have hM0 : (Lv.id0 P).c₀ + 3 * (stack.length + 1) ≤ P.M := by show 0 + _ ≤ _; omega
  exact f4 hSup stack (Lv.id0 P) η (FlatAnchor.flat η) ρ σs cx.ret Rs hM0 (relW_id0 hE.2.1 hbl) hE.1 hStk hRs hK


/-! One plan start `P.N` above both the supply bound and the stack's word labels. -/

def envB (env : Env) : Nat := env.foldr (fun e n => max n (wsB e.2.2)) 0
def stkB (stack : List Frame) : Nat := stack.foldr (fun f n => max n (envB f.env)) 0

theorem envB_lt : ∀ (env : Env), ∀ e ∈ env, ∀ w ∈ e.2.2, ∀ a g, w.val = .loc a g → a.label < envB env
  | [], e, he => by cases he
  | e0 :: env, e, he => by
    intro w hw a g hv
    unfold envB; simp only [List.foldr_cons]
    rcases List.mem_cons.1 he with rfl | he'
    · exact Nat.lt_of_lt_of_le (wsB_lt _ w hw a g hv) (Nat.le_max_right _ _)
    · exact Nat.lt_of_lt_of_le (envB_lt env e he' w hw a g hv) (Nat.le_max_left _ _)

theorem stkB_lt : ∀ (stack : List Frame), ∀ f ∈ stack, ∀ e ∈ f.env, ∀ w ∈ e.2.2, ∀ a g, w.val = .loc a g →
    a.label < stkB stack
  | [], f, hf => by cases hf
  | f0 :: st, f, hf => by
    intro e he w hw a g hv
    unfold stkB; simp only [List.foldr_cons]
    rcases List.mem_cons.1 hf with rfl | hf'
    · exact Nat.lt_of_lt_of_le (envB_lt _ e he w hw a g hv) (Nat.le_max_right _ _)
    · exact Nat.lt_of_lt_of_le (stkB_lt st f hf' e he w hw a g hv) (Nat.le_max_left _ _)

theorem StkLt_of_le {P : Plan} {stack : List Frame} (h : stkB stack ≤ P.N) : StkLt P stack :=
  fun f hf e he w hw a g hv => Nat.lt_of_lt_of_le (stkB_lt stack f hf e he w hw a g hv) h

theorem Plan.Tail_mono {P : Plan} {N N' : Nat} (h : N ≤ N') {l : WeakMem.AllocLabel} (ht : P.Tail N' l) :
    P.Tail N l := by
  obtain ⟨k, hk, e⟩ := ht; exact ⟨k, Nat.le_trans h hk, e⟩

theorem RsSup_of {P : Plan} {N5 : Nat} {Rs : Res} (hN : N5 ≤ P.N) (h : ∀ l, P.Tail N5 l → Rs (.own l) = 0) :
    RsSup P Rs := fun l hl => h l (Plan.Tail_mono hN hl)

theorem TailBlank_of {P : Plan} {N5 : Nat} {η : TEnv} (hN : N5 ≤ P.N)
    (h : ∀ m, P.Tail N5 m → η.sto m = none ∧ η.box m = none ∧ η.ini m = 0 ∧ η.rini m = 0 ∧ η.pfr m = none ∧
      ¬ η.seen m) : TailBlank P η := fun m hm => h m (Plan.Tail_mono hN hm)

/-- The plan with `N := max N5 (stkB stack)` meets both bounds. -/
def planAt (base n i M N5 : Nat) (hn : 0 < n) (hM : 0 < M) (stack : List Frame) : Plan :=
  { base := base, n := n, i := i, M := M, N := max N5 (stkB stack), hn := hn, hM := hM }

theorem planAt_ok (base n i M N5 : Nat) (hn : 0 < n) (hM : 0 < M) (stack : List Frame) :
    N5 ≤ (planAt base n i M N5 hn hM stack).N ∧ StkLt (planAt base n i M N5 hn hM stack) stack :=
  ⟨Nat.le_max_left _ _, StkLt_of_le (Nat.le_max_right _ _)⟩

end TermSound.Flat
