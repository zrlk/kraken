import WeakCore.TermCohLe
import WeakCore.TermInterf

/-! # TermOwnCoh: `OwnCohInv` as a `SysInvN` clause

`TermCohLe.OwnCohInv` (at every own private cell the thread's coherence is at most its
`vWr`) for every thread at every cut, kept by every event:

* the stepper's thread step: `TermCohLe.ownCohInv_step` (at the step's witness);
* an idle thread under another thread's step: its private cells are the same
  (`TermInterf.Priv_gfoot`, `cutSto_gfoot_priv`), its view unchanged;
* a promise step: views unchanged, own cells kept, frontiers only appear
  (`TermCohLe.OwnCohInv_mono`);
* the initial configuration with empty memory: no own cell has a word (`OwnOKPF`).
-/

namespace TermOwnCoh
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermMain TermCohLe

/-- `OwnCohInv` at a cut does not depend on the cut's seen set. -/
theorem ownCoh_seen {Eg : GEnv} {i : Nat} {S S' : AllocLabel → Prop} {s : St}
    (h : OwnCohInv (Cut Eg i S) s) : OwnCohInv (Cut Eg i S') s := h

/-- **An idle thread across a global step** (`GFoot` of another thread): its private
cells are the same, so `OwnCohInv` at an unchanged state transfers. -/
theorem ownCoh_gfoot {g : G} {Eg Eg2 : GEnv} {n n' : Nat} {v : Ts} (hf : GFoot g Eg Eg2 n n' v)
    {j : Nat} (hj : j ≠ g.i) (f : Nat → List Ts) {S S' : AllocLabel → Prop} {s : St}
    (h : OwnCohInv (Cut Eg j S) s) : OwnCohInv (Cut (Eg2.withFp f) j S') s := by
  intro l c hsl ho hpn o hin
  have hP : Priv (Cut (Eg2.withFp f) j S') l := ⟨⟨c, hsl, ho⟩, hpn⟩
  have hP0 : Priv (Cut Eg j S) l := (TermInterf.Priv_gfoot hf hj f S S' l).1 hP
  have e := TermInterf.cutSto_gfoot_priv hf f S hP0
  have hs0 : (Cut Eg j S).sto l = some c := by
    show cutSto Eg j l = some c
    rw [← e]; exact hsl
  exact h l c hs0 ho hP0.2 o hin

/-- **A global environment with the same cells and only new frontiers** (a promise
step's `EgP`): `OwnCohInv` at an unchanged state transfers. -/
theorem ownCoh_sto {Eg Eg' : GEnv} {j : Nat} {S S' : AllocLabel → Prop} {s : St}
    (hs : Eg'.sto = Eg.sto) (hp : ∀ l, Eg'.pfr l = none → Eg.pfr l = none)
    (h : OwnCohInv (Cut Eg j S) s) : OwnCohInv (Cut Eg' j S') s := by
  intro l c hsl ho hpn o hin
  have h1 : Eg'.sto l = some c := cutSto_sub hsl
  rw [hs] at h1
  exact h l c (cutSto_own h1 ho) ho (hp l hpn) o hin

/-- `plantG` keeps the cells and only adds frontiers. -/
theorem plantG_pfr_none {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {l : AllocLabel}
    (h : (plantG Eg P N).pfr l = none) : Eg.pfr l = none := by
  unfold plantG at h
  cases e : P l with
  | none => simp only [e] at h; exact h
  | some f => simp only [e] at h; cases h

/-- **The initial configuration**: at an empty memory, no own cell has a word
(`OwnOKPF`: each word's coherence message exists), so `OwnCohInv` holds. -/
theorem ownCoh_empty {E : TEnv} {mem : Memory} {pairs : List Ts} {th : TTh}
    (hown : OwnOKPF E mem pairs th.vs th.promises) (hmem : mem = #[]) : OwnCohInv E (stOf mem pairs th) := by
  intro l c hsl ho _ o hin
  obtain ⟨vals, hcv, hlat, -⟩ := hown l c hsl ho
  obtain ⟨⟨m, hm, -⟩, -⟩ := hlat o _ (List.getElem?_eq_getElem (hin.lt hcv))
  rw [hmem] at hm
  simp at hm

/-- `TermOwnCohZ.OwnCohZ` (the `SysInvN` clause) is `OwnCohInv`. -/
theorem ownCohZ_iff {E : TEnv} {s : St} : TermOwnCohZ.OwnCohZ E s ↔ OwnCohInv E s := Iff.rfl

/-- **The initial configuration** (`SysInvW` at an empty memory). -/
theorem ownCoh_initW {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) (hmem : c.mem = #[]) :
    ∀ i th (S : AllocLabel → Prop), c.ths[i]? = some th →
      TermOwnCohZ.OwnCohZ (Cut Eg i S) (stOf c.mem c.pairs th) := by
  intro i th S hth
  obtain ⟨S0, -, -, hm0, -⟩ := h.thr i th hth
  exact ownCoh_seen (S := S0) (ownCoh_empty hm0.2.1 hmem)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **The former field `ownCohInv`** from the `SysInvN` clause. -/
theorem ownCohInvT_of : OwnCohInvT p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y
  rw [Y.1]
  exact X.inv.ownCoh i th S X.hth

/-- **The stepper after its thread step**, at the step's witness `E'`. -/
theorem ownCoh_stepper
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ) :
    OwnCohInv E' (stOf r.1 r.2.1 r.2.2) :=
  ownCohInvT_step ownCohInvT_of X Y Z

end

end TermOwnCoh

#print axioms TermOwnCoh.ownCoh_seen
#print axioms TermOwnCoh.ownCoh_gfoot
#print axioms TermOwnCoh.ownCoh_empty
#print axioms TermOwnCoh.ownCoh_sto
#print axioms TermOwnCoh.plantG_pfr_none
#print axioms TermOwnCoh.ownCohZ_iff
#print axioms TermOwnCoh.ownCoh_initW
#print axioms TermOwnCoh.ownCohInvT_of
#print axioms TermOwnCoh.ownCoh_stepper
