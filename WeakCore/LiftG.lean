import WeakCore.CopyPlan
import WeakCore.EtaC
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! Lift side (L2/D1): the canonical per-position relabel `gc`.  A word is sent to its copy (`cpy`)
exactly at a `pub` reference position whose ♭ reading is exempt (`exmW`); everywhere else by `σ`.
`gc` reads only the type, the runtime shape, the words and `η`'s box/pfr/seen/sto — never `ρ`. -/

section
variable (cpy σ : WeakMem.AllocLabel → WeakMem.AllocLabel) (Cp : WeakMem.AllocLabel → Prop)
  (bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel)

/-- A label/view pair that the ♭ reading could only have typed by the exemption. -/
def Fr1 (η : TEnv) (l : WeakMem.AllocLabel) (v : WeakMem.Ts) : Prop :=
  ∃ f, η.pfr l = some f ∧ (η.seen l ∨ f ≤ v)

/-- A single-word `pub` reference that needs its copy. -/
def exmW (η : TEnv) (ws : List Word) : Prop :=
  ∃ a, ws.map (·.val) = [.loc a 0] ∧ Cp a.label ∧ ¬ FreshW η ws

/-- `shI` on the arm type's own tier (inverse to `unA` after `shI`). -/
def shIA (t : Ty) (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel :=
  if sumHead t then shI t.tier G else G

/-- Shift a type-variable oracle under a binder: the new variable 0 is read by `σ`. -/
def shT (T : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) :
    Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel
  | 0, _, _ => fun _ => σ
  | k + 1, rt, ws => T k rt ws

open Classical in
/-- The pub-position relabel. -/
noncomputable def pubG (η : TEnv) (ws : List Word) : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel :=
  fun i => if i = 0 ∧ exmW Cp η ws then cpy else σ

open Classical in
/-- `gc T TU η t rt ws`: `T` is the type-variable oracle at `η`, `TU` the one at `η.unsee` (box payloads are read
there).  At a boxed-sum pointer whose arm is unboxed, the pointer goes to the box VARIANT `bv x k`, `k` the code
(`PCode.enc`) of the payload's own canonical relabel at `η.unsee` (nested pointers get nested variants). -/
noncomputable def gc (T TU : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (η : TEnv) :
    Ty → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel
  | .ptr μ _, _, ws => match μ with | .pub => pubG cpy σ Cp η ws | _ => fun _ => σ
  | .ptrOpt μ _, _, ws => match μ with | .pub => pubG cpy σ Cp η ws | _ => fun _ => σ
  | .loc μ _, _, ws => match μ with | .pub => pubG cpy σ Cp η ws | _ => fun _ => σ
  | .refine t _, rt, ws => gc T TU η t rt ws
  | .iex b, rt, ws => match rt with | .iex _ rb => gc T TU η b rb ws | _ => fun _ => σ
  | .prod a b, rt, ws => match rt with
    | .prod ra rb => match ra.wc with
      | some n => fun i => if i < n then gc T TU η a ra (ws.take n) i else gc T TU η b rb (ws.drop n) (i - n)
      | none => fun _ => σ
    | _ => fun _ => σ
  | .sum a b, rt, ws => match rt with
    | .sum n (.sum Ra Rb) =>
      if (Ty.sum Ra Rb).tier = .boxed then
        match n, ws.map (fun w : Word => w.val) with
        | some (s + 1), [WeakMem.Val.loc x 0] =>
          match η.box x.label with
          | some B =>
            if B.tag - s < (armsOf Ra).length then
              (if isBoxed Ra = true then gc T TU η a (vsh s (shp Ra)) ws else
                match ofArm Ra (B.tag - s) B.pay with
                | some q => fun _ y => bv y (PCode.enc σ cpy bv (shIA Ra (gc TU TU η.unsee a (shp Ra) q)) B.pay.length)
                | none => fun _ => σ)
            else (if isBoxed Rb = true then gc T TU η b (vsh (s + (armsOf Ra).length) (shp Rb)) ws else
                match ofArm Rb (B.tag - s - (armsOf Ra).length) B.pay with
                | some q => fun _ y => bv y (PCode.enc σ cpy bv (shIA Rb (gc TU TU η.unsee b (shp Rb) q)) B.pay.length)
                | none => fun _ => σ)
          | none => fun _ => σ
        | _, _ => fun _ => σ
      else
        match decodeArm (Ty.sum Ra Rb).tier (armsOf (.sum Ra Rb)) ws with
        | some (j, p) =>
          if p = [] then fun _ => σ else
          if j < (armsOf Ra).length then
            (match ofArm Ra j p with
             | some q => unI (Ty.sum Ra Rb).tier (shIA Ra (gc T TU η a (shp Ra) q))
             | none => fun _ => σ)
          else
            (match ofArm Rb (j - (armsOf Ra).length) p with
             | some q => unI (Ty.sum Ra Rb).tier (shIA Rb (gc T TU η b (shp Rb) q))
             | none => fun _ => σ)
        | none => fun _ => σ
    | _ => fun _ => σ
  | .tvar k, rt, ws => T k rt ws
  | .tex _ b, rt, ws => match rt with | .tex _ rb => gc (shT σ T) (shT σ TU) η b rb ws | _ => fun _ => σ
  | .mu b, rt, ws => gc (shT σ T) (shT σ TU) η b rt ws
  | .iall b, rt, ws => gc T TU η b rt ws
  | .tid, _, ws => pubG cpy σ Cp η ws
  | _, _, _ => fun _ => σ

/-- Exemption soundness of a relabel: each position is `σ` or the copy, and the copy only at a loc word
that needs it. -/
def ExS (η : TEnv) (ws : List Word) (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) : Prop :=
  ∀ i, G i = σ ∨ (G i = cpy ∧ ∀ w a g, ws[i]? = some w → w.val = .loc a g → Cp a.label ∧ ¬ Fr1 η a.label w.view) ∨
    ∃ k, G i = fun y => bv y k



end

section
variable {cpy σ : WeakMem.AllocLabel → WeakMem.AllocLabel} {Cp : WeakMem.AllocLabel → Prop}
  {bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel}

theorem unI_shIA (tr : Tier) (t : Ty) (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (i : Nat) :
    unI tr (shIA t G) i = G (ixA t (ixU tr i)) := by
  unfold ixA shIA
  cases tr <;> simp only [unI, ixU] <;> (by_cases h : sumHead t = true <;> simp only [h, if_true, if_false] <;>
    cases ht : t.tier <;> simp [shI, ht])

theorem ExS_cst (η : TEnv) (ws : List Word) : ExS cpy σ Cp bv η ws (fun _ => σ) := fun _ => Or.inl rfl

theorem ExS_bv (η : TEnv) (ws : List Word) (k : Nat) : ExS cpy σ Cp bv η ws (fun _ y => bv y k) :=
  fun _ => Or.inr (Or.inr ⟨k, rfl⟩)

theorem pubG_ExS (η : TEnv) (ws : List Word) : ExS cpy σ Cp bv η ws (pubG cpy σ Cp η ws) := by
  intro i
  by_cases h : i = 0 ∧ exmW Cp η ws
  · refine Or.inr (Or.inl ⟨by simp [pubG, h], fun w a g hw hv => ?_⟩)
    obtain ⟨rfl, a', ha', hc, hF⟩ := h
    rcases ws with _ | ⟨w0, _ | ⟨w1, ws⟩⟩
    · simp at ha'
    · simp at hw; subst hw; simp at ha'; rw [hv] at ha'; cases ha'
      refine ⟨hc, fun ⟨f, hf, hs⟩ => hF fun b hb => ?_⟩
      simp [hv] at hb; subst hb
      exact ⟨f, hf, hs.imp id (fun hl w' hw' => by simp at hw'; subst hw'; exact hl)⟩
    · simp at ha'
  · exact Or.inl (by simp [pubG, h])

end
end TermSound.Flat
