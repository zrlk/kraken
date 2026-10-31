import WeakCore.Emb
/-! **PubPos**: the value-keyed pub-position predicate, moved here from DPub/LiftG
so that the ♭ refine arm (VRb2/VRz/VRRz/VRRB) can key D5 (b) on it.  Text unchanged from DPub (with its tid arm)
and LiftG (`ixU`/`ixA`). -/
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

def ixU : Tier → Nat → Nat
  | .wide, i => i - 1
  | _, i => i

def ixA (t : Ty) (k : Nat) : Nat := if sumHead t ∧ t.tier = .wide then k + 1 else k

/-- Shift a pub-position oracle under a type binder (the bound variable is never pub). -/
def shPT (PT : Nat → Shp → List Word → Nat → Bool) : Nat → Shp → List Word → Nat → Bool
  | 0, _, _ => fun _ => false
  | k + 1, rt, ws => PT k rt ws

/-- `pp PT bx t rt ws i`: position `i` of `ws` reaches a pub head (`gc`'s skeleton; `PT` the tvar oracle,
`bx` the box map). -/
def pp (PT : Nat → Shp → List Word → Nat → Bool) (bx : WeakMem.AllocLabel → Option Box) :
    Ty → Shp → List Word → Nat → Bool
  | .ptr μ _, _, _ => match μ with | .pub => fun i => decide (i = 0) | _ => fun _ => false
  | .ptrOpt μ _, _, _ => match μ with | .pub => fun i => decide (i = 0) | _ => fun _ => false
  | .loc μ _, _, _ => match μ with | .pub => fun i => decide (i = 0) | _ => fun _ => false
  | .refine t _, rt, ws => pp PT bx t rt ws
  | .iex b, rt, ws => match rt with | .iex _ rb => pp PT bx b rb ws | _ => fun _ => false
  | .prod a b, rt, ws => match rt with
    | .prod ra rb => match ra.wc with
      | some n => fun i => if i < n then pp PT bx a ra (ws.take n) i else pp PT bx b rb (ws.drop n) (i - n)
      | none => fun _ => false
    | _ => fun _ => false
  | .sum a b, rt, ws => match rt with
    | .sum n (.sum Ra Rb) =>
      if (Ty.sum Ra Rb).tier = .boxed then
        match n, ws.map (fun w : Word => w.val) with
        | some (s + 1), [WeakMem.Val.loc x 0] =>
          match bx x.label with
          | some B =>
            if B.tag - s < (armsOf Ra).length then
              (if isBoxed Ra = true then pp PT bx a (vsh s (shp Ra)) ws else fun _ => false)
            else (if isBoxed Rb = true then pp PT bx b (vsh (s + (armsOf Ra).length) (shp Rb)) ws else
              fun _ => false)
          | none => fun _ => false
        | _, _ => fun _ => false
      else
        match decodeArm (Ty.sum Ra Rb).tier (armsOf (.sum Ra Rb)) ws with
        | some (j, p) =>
          if p = [] then fun _ => false else
          if j < (armsOf Ra).length then
            (match ofArm Ra j p with
             | some q => fun i => pp PT bx a (shp Ra) q (ixA Ra (ixU (Ty.sum Ra Rb).tier i))
             | none => fun _ => false)
          else
            (match ofArm Rb (j - (armsOf Ra).length) p with
             | some q => fun i => pp PT bx b (shp Rb) q (ixA Rb (ixU (Ty.sum Ra Rb).tier i))
             | none => fun _ => false)
        | none => fun _ => false
    | _ => fun _ => false
  | .tvar k, rt, ws => PT k rt ws
  | .tex _ b, rt, ws => match rt with | .tex _ rb => pp (shPT PT) bx b rb ws | _ => fun _ => false
  | .mu b, rt, ws => pp (shPT PT) bx b rt ws
  | .iall b, rt, ws => pp PT bx b rt ws
  | .tid, _, _ => fun i => decide (i = 0)
  | _, _, _ => fun _ => false

/-- The witness oracle at `η`: a type variable reads its witness by the same recursion (closed). -/
def PTop (η : TEnv) : Nat → Shp → List Word → Nat → Bool :=
  fun k rt ws i => pp (fun _ _ _ _ => false) η.box (η.wit k) rt ws i

/-- **PubPos**: position 0 of the value reaches a pub reference head. -/
def PubPos (η : TEnv) (t : Ty) (rt : Shp) (ws : List Word) : Bool := pp (PTop η) η.box t rt ws 0

/-- The witness oracle at an extended box map `bx` (`PTopB η.box η = PTop η` by `rfl`). -/
def PTopB (bx : WeakMem.AllocLabel → Option Box) (η : TEnv) : Nat → Shp → List Word → Nat → Bool :=
  fun k rt ws i => pp (fun _ _ _ _ => false) bx (η.wit k) rt ws i

/-- **PubPosE** (P4: only at the 4 ♭ refine sites): `PubPos` at some box map extending `η.box`. -/
def PubPosE (η : TEnv) (t : Ty) (rt : Shp) (ws : List Word) : Prop :=
  ∃ bx : WeakMem.AllocLabel → Option Box, (∀ l B, η.box l = some B → bx l = some B) ∧
    pp (PTopB bx η) bx t rt ws 0 = true

example (η : TEnv) : PTopB η.box η = PTop η := rfl

theorem PubPosE_of {η : TEnv} {t : Ty} {rt : Shp} {ws : List Word} (h : PubPos η t rt ws = true) :
    PubPosE η t rt ws := ⟨η.box, fun _ _ h => h, h⟩

/-! pp value-congruence (the refine arm's antecedent now reads the words, so WLe/VEq
transports need it). -/
theorem VEq_take {ws ws' : List Word} (e : VEq ws ws') (n : Nat) : VEq (ws.take n) (ws'.take n) := by
  simp only [VEq, List.map_take] at e ⊢; rw [e]

theorem VEq_drop {ws ws' : List Word} (e : VEq ws ws') (n : Nat) : VEq (ws.drop n) (ws'.drop n) := by
  simp only [VEq, List.map_drop] at e ⊢; rw [e]

theorem decodeArm_none_vals {tr : Tier} {as : List Ty} {ws ws' : List Word} (e : VEq ws ws')
    (h : decodeArm tr as ws = none) : decodeArm tr as ws' = none := by
  rcases h' : decodeArm tr as ws' with _ | ⟨j, p⟩
  · rfl
  · obtain ⟨p', hp', -⟩ := decodeArm_vals e.symm h'; rw [h] at hp'; cases hp'

theorem ofArm_none_vals {t : Ty} {j : Nat} {p p' : List Word} (e : VEq p p') (h : ofArm t j p = none) :
    ofArm t j p' = none := by
  rcases h' : ofArm t j p' with _ | q
  · rfl
  · obtain ⟨q', hq', -⟩ := ofArm_vals e.symm h'; rw [h] at hq'; cases hq'

/-- An oracle respecting word values. -/
def PTVals (PT : Nat → Shp → List Word → Nat → Bool) : Prop :=
  ∀ k rt ws ws', VEq ws ws' → PT k rt ws = PT k rt ws'

theorem shPT_vals {PT : Nat → Shp → List Word → Nat → Bool} (h : PTVals PT) : PTVals (shPT PT) := by
  intro k rt ws ws' e
  cases k with
  | zero => rfl
  | succ k => exact h k rt ws ws' e

theorem pp_vals (bx : WeakMem.AllocLabel → Option Box) (t : Ty) :
    ∀ (PT : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws ws' : List Word),
    PTVals PT → VEq ws ws' → pp PT bx t rt ws = pp PT bx t rt ws' := by
  induction t with
  | refine t ψ ih => intro PT rt ws ws' hPT e; simp only [pp]; exact ih PT rt ws ws' hPT e
  | iall b ih => intro PT rt ws ws' hPT e; simp only [pp]; exact ih PT rt ws ws' hPT e
  | mu b ih => intro PT rt ws ws' hPT e; simp only [pp]; exact ih _ rt ws ws' (shPT_vals hPT) e
  | tvar k => intro PT rt ws ws' hPT e; simp only [pp]; exact hPT k rt ws ws' e
  | iex b ih =>
    intro PT rt ws ws' hPT e
    cases rt <;> simp only [pp]
    exact ih PT _ ws ws' hPT e
  | tex κ b ih =>
    intro PT rt ws ws' hPT e
    cases rt <;> simp only [pp]
    exact ih _ _ ws ws' (shPT_vals hPT) e
  | prod a b iha ihb =>
    intro PT rt ws ws' hPT e
    cases rt with
    | prod ra rb =>
      simp only [pp]
      rcases hn : ra.wc with _ | n
      · rfl
      · funext i
        by_cases hi : i < n
        · simp only [hi, if_true]; rw [iha PT ra _ _ hPT (VEq_take e n)]
        · simp only [hi, if_false]; rw [ihb PT rb _ _ hPT (VEq_drop e n)]
    | _ => simp only [pp]
  | sum a b iha ihb =>
    intro PT rt ws ws' hPT e
    cases rt with
    | sum n R =>
      cases R with
      | sum Ra Rb =>
        simp only [pp]
        by_cases htb : (Ty.sum Ra Rb).tier = .boxed
        · have hA : ∀ r, pp PT bx a r ws = pp PT bx a r ws' := fun r => iha PT r ws ws' hPT e
          have hB : ∀ r, pp PT bx b r ws = pp PT bx b r ws' := fun r => ihb PT r ws ws' hPT e
          simp only [htb, if_true, hA, hB]
          rw [show ws.map (fun w : Word => w.val) = ws'.map (fun w : Word => w.val) from e]
        · simp only [htb, if_false]
          rcases hd : decodeArm (Ty.sum Ra Rb).tier (armsOf (.sum Ra Rb)) ws with _ | ⟨j, p⟩
          · rw [decodeArm_none_vals e hd]
          · obtain ⟨p', hd', ep⟩ := decodeArm_vals e hd
            rw [hd']
            have hl : p.length = p'.length := by
              have := congrArg List.length ep; simpa using this
            by_cases hp0 : p = []
            · have hp0' : p' = [] := by subst hp0; exact List.length_eq_zero_iff.mp hl.symm
              simp only [hp0, hp0', if_true]
            · have hp0' : p' ≠ [] := fun h => hp0 (by subst h; exact List.length_eq_zero_iff.mp hl)
              simp only [hp0, hp0', if_false]
              by_cases hj : j < (armsOf Ra).length
              · simp only [hj, if_true]
                rcases hq : ofArm Ra j p with _ | q
                · rw [ofArm_none_vals ep hq]
                · obtain ⟨q', hq', eq⟩ := ofArm_vals ep hq
                  rw [hq']; dsimp only; funext i; rw [iha PT _ q q' hPT eq]
              · simp only [hj, if_false]
                rcases hq : ofArm Rb (j - (armsOf Ra).length) p with _ | q
                · rw [ofArm_none_vals ep hq]
                · obtain ⟨q', hq', eq⟩ := ofArm_vals ep hq
                  rw [hq']; dsimp only; funext i; rw [ihb PT _ q q' hPT eq]
      | _ => simp only [pp]
    | _ => simp only [pp]
  | _ => intro PT rt ws ws' _ _; simp only [pp]

theorem PTopB_vals (bx : WeakMem.AllocLabel → Option Box) (η : TEnv) : PTVals (PTopB bx η) := by
  intro k rt ws ws' e
  funext i
  simp only [PTopB]
  rw [pp_vals bx (η.wit k) _ rt ws ws' (fun _ _ _ _ _ => rfl) e]

theorem PubPosE_vals {η : TEnv} {t : Ty} {rt : Shp} {ws ws' : List Word} (e : VEq ws ws')
    (h : PubPosE η t rt ws') : PubPosE η t rt ws := by
  obtain ⟨bx, hb, hp⟩ := h
  exact ⟨bx, hb, by rw [pp_vals bx t _ rt ws ws' (PTopB_vals bx η) e]; exact hp⟩

theorem PubPosE_mono {η₁ η₂ : TEnv} {t : Ty} {rt : Shp} {ws : List Word} (hw : η₁.wit = η₂.wit)
    (hBx : ∀ l B, η₁.box l = some B → η₂.box l = some B) (h : PubPosE η₂ t rt ws) : PubPosE η₁ t rt ws := by
  obtain ⟨bx, hb, hp⟩ := h
  refine ⟨bx, fun l B h => hb l B (hBx l B h), ?_⟩
  have : PTopB bx η₁ = PTopB bx η₂ := by unfold PTopB; rw [hw]
  rw [this]; exact hp

end TermSound.Flat
