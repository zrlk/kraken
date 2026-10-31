import WeakCore.MergeQ
/-! **PubPosM**: `pp` / `PubPosE` under the merge relabelling `rl f` (for the
MergeR/MergeW refine arms).  `pp` reads the box map only through tags (`pp_tag`). -/
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

theorem pp_tag {bx bx' : WeakMem.AllocLabel → Option Box}
    (h : ∀ l, Option.map Box.tag (bx l) = Option.map Box.tag (bx' l)) (t : Ty) :
    ∀ (PT : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws : List Word), pp PT bx t rt ws = pp PT bx' t rt ws := by
  induction t with
  | refine t ψ ih => intro PT rt ws; simp only [pp]; exact ih PT rt ws
  | iall b ih => intro PT rt ws; simp only [pp]; exact ih PT rt ws
  | mu b ih => intro PT rt ws; simp only [pp]; exact ih _ rt ws
  | iex b ih => intro PT rt ws; cases rt <;> simp only [pp]; exact ih PT _ ws
  | tex κ b ih => intro PT rt ws; cases rt <;> simp only [pp]; exact ih _ _ ws
  | prod a b iha ihb =>
    intro PT rt ws
    have ea : ∀ r ws, pp PT bx a r ws = pp PT bx' a r ws := fun r ws => iha PT r ws
    have eb : ∀ r ws, pp PT bx b r ws = pp PT bx' b r ws := fun r ws => ihb PT r ws
    simp only [pp, ea, eb]
  | sum a b iha ihb =>
    intro PT rt ws
    have ea : ∀ r ws, pp PT bx a r ws = pp PT bx' a r ws := fun r ws => iha PT r ws
    have eb : ∀ r ws, pp PT bx b r ws = pp PT bx' b r ws := fun r ws => ihb PT r ws
    cases rt with
    | sum n R =>
      cases R with
      | sum Ra Rb =>
        simp only [pp, ea, eb]
        by_cases htb : (Ty.sum Ra Rb).tier = .boxed
        · simp only [htb, if_true]
          generalize ws.map (·.val) = V
          rcases n with _ | _ | s
          all_goals
            first
            | rfl
            | (rcases V with _ | ⟨v, V⟩
               · rfl
               · cases v <;> first
                   | rfl
                   | (rename_i x g
                      cases g <;> rcases V with _ | ⟨v2, V⟩ <;> try rfl
                      have hx := h x.label
                      rcases h1 : bx x.label with _ | B <;> rcases h2 : bx' x.label with _ | B' <;>
                        simp only [h1, h2, Option.map, Option.some.injEq, reduceCtorEq] at hx ⊢
                      rw [hx]))
        · simp only [htb, if_false]
      | _ => simp only [pp]
    | _ => simp only [pp]
  | _ => intro PT rt ws; rfl

theorem pp_rl (f : WeakMem.AllocLabel → WeakMem.AllocLabel) (bx : WeakMem.AllocLabel → Option Box) (t : Ty) :
    ∀ (PT : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws : List Word),
    pp PT bx t rt (ws.map (rl f)) = pp (fun k rt ws => PT k rt (ws.map (rl f))) (fun l => bx (f l)) t rt ws := by
  induction t with
  | refine t ψ ih => intro PT rt ws; simp only [pp]; exact ih PT rt ws
  | iall b ih => intro PT rt ws; simp only [pp]; exact ih PT rt ws
  | tvar k => intro PT rt ws; rfl
  | mu b ih =>
    intro PT rt ws; simp only [pp]; rw [ih]
    congr 1; funext k rt' ws'; cases k <;> rfl
  | iex b ih => intro PT rt ws; cases rt <;> simp only [pp]; exact ih PT _ ws
  | tex κ b ih =>
    intro PT rt ws; cases rt <;> simp only [pp]
    rw [ih]; congr 1; funext k rt' ws'; cases k <;> rfl
  | prod a b iha ihb =>
    intro PT rt ws
    cases rt with
    | prod ra rb =>
      simp only [pp]
      rcases hn : ra.wc with _ | n
      · rfl
      · funext i
        have e1 : (ws.map (rl f)).take n = (ws.take n).map (rl f) := by simp
        have e2 : (ws.map (rl f)).drop n = (ws.drop n).map (rl f) := by simp
        by_cases hi : i < n
        · simp only [hi, if_true]; rw [e1, iha]
        · simp only [hi, if_false]; rw [e2, ihb]
    | _ => simp only [pp]
  | sum a b iha ihb =>
    intro PT rt ws
    cases rt with
    | sum n R =>
      cases R with
      | sum Ra Rb =>
        have hA : ∀ r, pp PT bx a r (ws.map (rl f)) = pp (fun k rt ws => PT k rt (ws.map (rl f))) (fun l => bx (f l)) a r ws :=
          fun r => iha PT r ws
        have hB : ∀ r, pp PT bx b r (ws.map (rl f)) = pp (fun k rt ws => PT k rt (ws.map (rl f))) (fun l => bx (f l)) b r ws :=
          fun r => ihb PT r ws
        simp only [pp]
        by_cases htb : (Ty.sum Ra Rb).tier = .boxed
        · simp only [htb, if_true, hA, hB, vals_rl]
          generalize ws.map (·.val) = V
          rcases n with _ | _ | s
          all_goals
            first
            | rfl
            | (rcases V with _ | ⟨v, V⟩
               · rfl
               · cases v <;> first
                   | rfl
                   | (rename_i x g
                      cases g <;> rcases V with _ | ⟨v2, V⟩ <;> rfl))
        · simp only [htb, if_false]
          rw [decodeArm_rl]
          rcases hd : decodeArm (Ty.sum Ra Rb).tier (armsOf (.sum Ra Rb)) ws with _ | ⟨j, p⟩
          · rfl
          · simp only [Option.map]
            by_cases hp0 : p = []
            · subst hp0; rfl
            · have hp0' : p.map (rl f) ≠ [] := by simpa using hp0
              simp only [hp0, hp0', if_false]
              by_cases hj : j < (armsOf Ra).length
              · simp only [hj, if_true]
                rw [ofArm_rl]
                rcases hq : ofArm Ra j p with _ | q
                · rfl
                · simp only [Option.map]; funext i; rw [iha]
              · simp only [hj, if_false]
                rw [ofArm_rl]
                rcases hq : ofArm Rb (j - (armsOf Ra).length) p with _ | q
                · rfl
                · simp only [Option.map]; funext i; rw [ihb]
      | _ => simp only [pp]
    | _ => simp only [pp]
  | ptr μ u _ => intro PT rt ws; cases μ <;> rfl
  | ptrOpt μ u _ => intro PT rt ws; cases μ <;> rfl
  | loc μ u _ => intro PT rt ws; cases μ <;> rfl
  | _ => intro PT rt ws; rfl

/-- `PubPosE` pulls back along the merge relabelling (boxes kept up to payload, tags equal). -/
theorem PubPosE_rl {f : WeakMem.AllocLabel → WeakMem.AllocLabel} {η₁ η₂ : TEnv} {t : Ty} {rt : Shp} {ws : List Word}
    (hw : η₁.wit = η₂.wit) (hbox : ∀ m B, η₁.box m = some B → ∃ B', η₂.box (f m) = some B' ∧ B'.tag = B.tag)
    (hp : PubPosE η₂ t rt (ws.map (rl f))) : PubPosE η₁ t rt ws := by
  obtain ⟨bx, hbx, hp⟩ := hp
  let bx₁ : WeakMem.AllocLabel → Option Box := fun l => match η₁.box l with | some B => some B | none => bx (f l)
  have htag : ∀ l, Option.map Box.tag ((fun l => bx (f l)) l) = Option.map Box.tag (bx₁ l) := by
    intro l
    show Option.map Box.tag (bx (f l)) = Option.map Box.tag (match η₁.box l with | some B => some B | none => bx (f l))
    rcases h : η₁.box l with _ | B
    · rfl
    · obtain ⟨B', h2, ht⟩ := hbox l B h
      rw [hbx _ _ h2]; simp [ht]
  refine ⟨bx₁, fun l B h => by show (match η₁.box l with | some B => some B | none => bx (f l)) = _; rw [h], ?_⟩
  have e1 := pp_rl f bx t (PTopB bx η₂) rt ws
  have eo : (fun k rt ws => PTopB bx η₂ k rt (ws.map (rl f))) = PTopB bx₁ η₁ := by
    funext k rt' ws'
    show pp (fun _ _ _ _ => false) bx (η₂.wit k) rt' (ws'.map (rl f)) = pp (fun _ _ _ _ => false) bx₁ (η₁.wit k) rt' ws'
    rw [pp_rl f bx (η₂.wit k), ← hw, pp_tag htag]
  rw [e1, eo, pp_tag htag] at hp
  exact hp

end TermSound.Flat
