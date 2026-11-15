import WeakCore.TermC1Guards
import WeakCore.TermSpawnDefs
import WeakCore.Syntax

/-! Spawn scope: checks against `opShareOK`'s spawn arm (TermC1Defs), and the initial-kid lemma that a kid's type
arguments carry no second-class capability. -/
namespace TermC1F10
open CoreLang CoreTerm CoreTyping TermScope TermC1 TermTv TermSound TermSpawn

/-- A `bor` capability packed into `∃a. Cap[bor, a]` and spawned. -/
def s0src : String := "
type CP = exists a. Cap[bor, a]

def kidC(k : CP) : Unit = ret ()

def capSpawn(u : Unit) : Unit =
  let z = zero[U64]
  let p = new[U64] z
  let <r, q, t0> = region p
  let c = borrow bor t0
  let pk = pack c at r : exists a. Cap[bor, a]
  let h = spawn kidC pk : exists a. Cap[bor, a]
  let e = endBorrow t0
  let s = store q z
  ret ()
"
def S0 : Prog := match Syntax.parseProg s0src with | .ok p => p | .error _ => []
#guard S0.length == 2
#guard (checkProg S0 matches .ok _)
-- the program type-checks, and (δ) the c1 scope admits the second-class spawned value
#guard ProgScopeOKW1 S0 == true

/-- The `W1` case: a spawn of a bare `∃a. Cap[rd, a]` parameter, region-free; admitted under δ. -/
def w1src : String := "
type CR = exists a. Cap[rd, a]

def kidR(k : CR) : Unit = ret ()

def w1(c : CR) : Unit =
  let h = spawn kidR c : exists a. Cap[rd, a]
  ret ()
"
def W1P : Prog := match Syntax.parseProg w1src with | .ok p => p | .error _ => []
#guard W1P.length == 2
#guard (checkProg W1P matches .ok _)
#guard ProgScopeOKW1 W1P == true

/-- spawn value types / type arguments, deep. -/
def spawnTys : Expr → List Ty
  | .let_ _ (.spawn _ _ T ts) e => (T :: ts) ++ spawnTys e
  | .let_ _ (.spawnI _ _ _ T ts) e => (T :: ts) ++ spawnTys e
  | .let_ _ _ e | .split _ _ _ e | .unpack _ _ _ e | .unpackT _ _ _ e | .region _ _ _ _ e | .openPub _ _ _ _ e => spawnTys e
  | .case _ _ e₁ _ e₂ | .ifnull _ e₁ _ e₂ | .parity _ _ e₁ e₂ | .ifeq _ _ e₁ e₂ => spawnTys e₁ ++ spawnTys e₂
  | .cas _ _ _ _ _ _ ok fail | .casp _ _ _ _ _ _ _ _ ok fail => spawnTys ok ++ spawnTys fail
  | _ => []
-- census: 51 programs, none spawns a second-class type, so the rule changes no row; the acceptance set is pinned
-- by TermC1Guards's own guards (superset + exactly `newRows`), which rebuild green against the edited Defs
#guard TermC1Guards.corpusAll.length == 51
#guard TermC1Guards.corpusAll.all fun (_, p) => p.all fun d => (spawnTys d.body).all (!·.secondClass)
#eval IO.println s!"W1-accepted corpusAll rows: {(TermC1Guards.corpusAll.filter fun (_, p) => ProgScopeOKW1 p).length}/51"

theorem mem_zip_right {α β : Type} : ∀ {as : List α} {bs : List β} {b : β}, as.length = bs.length → b ∈ bs →
    ∃ a, (a, b) ∈ as.zip bs
  | [], [], _, _, hb => by simp at hb
  | a :: as, b' :: bs, b, hl, hb => by
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨a, by simp⟩
      · obtain ⟨a', ha'⟩ := mem_zip_right (as := as) (Nat.succ.inj hl) hb
        exact ⟨a', List.mem_cons_of_mem _ ha'⟩

/-- `instantiate` admits each type argument, so none is second-class (`admitsIn`, CoreTerm:1501). -/
theorem instantiate_noSecond {cx : Cx} {d : Decl} {is : List String} {ts : List Ty} {at_ rt : Ty}
    (h : instantiate cx d is ts = .ok (at_, rt)) : ∀ t ∈ ts, t.secondClass = false := by
  obtain ⟨hl, ha⟩ := instantiate_admits h
  intro t ht
  obtain ⟨κ, hk⟩ := mem_zip_right hl.symm ht
  have := ha κ t hk
  simp only [admitsIn, Bool.and_eq_true, Bool.not_eq_true'] at this
  first | exact this.1.1.1.1.1.1.1.2 | exact this.1.1.1.1.1.1.1.1.2 | exact this.1.1.1.1.1.1.1.1.1.2

theorem tailCheck_noSecond {p : Prog} {cx : Cx} {f : String} {is : List String} {a : At} {ts : List Ty}
    (h : tailCheck p cx f is a ts = .ok ()) : ∀ t ∈ ts, t.secondClass = false := by
  unfold tailCheck at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hi
  exact instantiate_noSecond hi

/-- An initial kid's type arguments carry no second-class capability: KidOK's entry check
(TermSpawnDefs:100-101) is a tail call, whose `instantiate` admits each argument. -/
theorem kidOK_ts_noSecond {p : Prog} {rt : Ty} {kd : Kid} (h : KidOK p rt kd) :
    ∀ t ∈ kd.ts, t.secondClass = false := by
  obtain ⟨r, hc, -⟩ := h.2.2.2.2.2.2.1
  exact tailCheck_noSecond (by simpa [check_tail] using hc)

end TermC1F10

#print axioms TermC1F10.instantiate_noSecond
#print axioms TermC1F10.tailCheck_noSecond
#print axioms TermC1F10.kidOK_ts_noSecond
