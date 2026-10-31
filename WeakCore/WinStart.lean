import WeakCore.WrIniInst
import WeakCore.AnchorFrameTyping
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
/-! The ♭ window start (`OwnXLeB` at the anchor), port of W TermOwnX2.ownXLe_start(_le). -/
namespace FlatWinStart
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain TermTyped
  TermOwnX2
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermOwnX2.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem MemHeldP_B {E : TEnv} {s : St} {H : Res} (h : MemHeldP E s H) : MemHeldPB E s H := by
  obtain ⟨L, Rl, h1, h2, h3, h4, h5⟩ := h
  refine ⟨L, Rl, h1, h2, h3, h4, fun l hl => ⟨(h5 l hl).1, fun c hc => ?_⟩⟩
  obtain ⟨vals, q1, q2⟩ := (h5 l hl).2 c hc
  exact ⟨vals, q1, FlatAnchor.CellOKR_B q2⟩

theorem ext_REB {p : Prog} {E : TEnv} {th : TTh} {Tot : Res} (h : ThInvREB glb gnum gi p E th Tot) : ExtB E E := by
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, -⟩ := h
  rw [← hCE]; exact Ext_reflB (Coh_CEB η) (CohR_CEB η)

/-- **♭ `OwnXLe` at any bound** at a `SysInvN` configuration, given the anchored `ContB`. -/
theorem ownXLeB_start_le {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {x : AllocLabel} {cl : Cell} {n : Nat} {S : AllocLabel → Prop} (hinv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hth : c.ths[i]? = some th)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S) (hsto : Eg.sto x = some cl)
    (hin : cl.owner = some i ∨ Eg.pfr x ≠ none) (hle : (Tot i + HP i) (.own x) ≤ n)
    (hK : FlatAnchor.ContB c.lbase c.n i p th (Cut Eg i S)) : OwnXLeB p k arch (Cut Eg i S) i x n c := by
  have hB := FlatAnchor.base_shape hinv.clo hS hK (FlatAnchor.rsFresh_of hinv hth) hinv.rle
  obtain ⟨hRE, -, hm, hP, -, -⟩ := hS
  simp only [Res.add_apply] at hle
  exact ⟨th, Cut Eg i S, Tot i, HP i, hth, hB.1, hB.2.1, MemHeldP_B hP, hinv.bf, stoNIE_cut hinv.stoNI,
    cut_sto_ne hsto hin, hle, ext_REB hB.1,
    anchR_start hm (hinv.riniCoh i th S hth) (fun l cl f hs hp => hinv.frlt l cl f (cutSto_sub hs) hp),
    (hinv.tyRec hth S).1, (hinv.tyRec hth S).2, fun _ => Nat.le_refl _, fun h => h⟩

/-- **♭ `OwnXLe 1`** at a `SysInvN` configuration (the window chain's start). -/
theorem ownXLeB_start {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {x : AllocLabel} {cl : Cell} {S : AllocLabel → Prop} (hinv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hth : c.ths[i]? = some th)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S) (hsto : Eg.sto x = some cl)
    (hin : cl.owner = some i ∨ Eg.pfr x ≠ none) (hK : FlatAnchor.ContB c.lbase c.n i p th (Cut Eg i S)) :
    OwnXLeB p k arch (Cut Eg i S) i x 1 c :=
  ownXLeB_start_le hinv hth hS hsto hin
    (Nat.le_trans (Nat.le_add_right _ _) (TermOwnNet.ownNet_one hinv x (lt_size_of hth))) hK
end FlatWinStart
