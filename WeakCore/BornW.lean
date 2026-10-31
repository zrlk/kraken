import WeakCore.BornU
import WeakCore.EtaO
/-! **BornW** (ownXLe_born): the oracle `hO` of `noHold_eta` at a FRESH label of the window, discharging
the window temporary `oFresh`.  At the `SysInvN` base the unborn label carries no `own` (`OwnFreshZ`), so the
U-variant `OwnXLeBU … x 0` (BornU) holds there; it runs along the solo window (`ownXLe_runAllSU`: the count
grows by one only at the step that gives `x` its cell); at the publish of `x` the cell exists, so the U bound
is the ♭ bound `OwnXLeB … x 1`, and `eta_oracle` (EtaO) concludes from the publish configuration itself. -/
namespace CertWinProof
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat
  TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat
  TermOwnK3.Flat TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The oracle at a fresh label of the window from `c` (thread `i`, `th`): formerly the window temporary
`oFresh`, now `oFresh_of`. -/
def OFresh (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (c : Cfg) (th : TTh) : Prop :=
  ∀ c1 th1 (y : String) (a : At) (e : Expr) (rt : Ty) (ws : List Word) (ad : Address) (j : Nat),
    Solo p k arch i c c1 → Certified p k arch c1 i → c1.ths[i]? = some th1 →
    th1.term = .let_ y (.publish a) e → evalAt th1.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
    th.nalloc ≤ j → ad.label = freshLabel c.lbase c.n i j →
    ∀ c0, Solo p k arch i c1 c0 → Certified p k arch c0 i → ∀ th0, c0.ths[i]? = some th0 → ¬ BufInitL th0 ad.label

/-- **The U window start**: at a `SysInvN` configuration, a fresh label of `i` (unborn) satisfies the U bound
at `0` (`OwnFreshZ`: no `own` of it in `i`'s frame or holding). -/
theorem ownXLeBU_start {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {S : AllocLabel → Prop} (hinv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hth : c.ths[i]? = some th)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S) {j : Nat}
    (hj : th.nalloc ≤ j) (hK : FlatAnchor.ContB c.lbase c.n i p th (Cut Eg i S)) :
    OwnXLeBU p k arch (Cut Eg i S) i (freshLabel c.lbase c.n i j) 0 c := by
  have hB := FlatAnchor.base_shape hinv.clo hS hK (FlatAnchor.rsFresh_of hinv hth) hinv.rle
  have hz := (hinv.ownF i th j hth hj).1 i (lt_size_of hth)
  obtain ⟨hRE, -, hm, hP, -, -⟩ := hS
  simp only [Res.add_apply] at hz
  exact ⟨th, Cut Eg i S, Tot i, HP i, hth, hB.1, hB.2.1, FlatWinStart.MemHeldP_B hP, hinv.bf,
    stoNIE_cut hinv.stoNI, trivial, by omega, FlatWinStart.ext_REB hB.1,
    anchR_start hm (hinv.riniCoh i th S hth) (fun l cl f hs hp => hinv.frlt l cl f (cutSto_sub hs) hp),
    (hinv.tyRec hth S).1, (hinv.tyRec hth S).2, trivial, fun h => h⟩

/-- At the publish of `x` the U bound at `0` is the ♭ bound at `1` (the publish needs `x`'s cell). -/
theorem ownXLeB_of_U {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel}
    {c : Cfg} {th1 : TTh} {y : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word} {ad : Address}
    (h : OwnXLeBU p k arch E0 i x 0 c) (hth1 : c.ths[i]? = some th1)
    (hterm : th1.term = .let_ y (.publish a) e) (hea : evalAt th1.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad 0]) (hx : ad.label = x) : OwnXLeB p k arch E0 i x 1 c := by
  obtain ⟨th, E, Tot, HP, hth, hT, hm, hP, hb, hn, -, hle, hX, hA, hTyE, hRc, -, hR⟩ := h
  rw [hth1] at hth
  cases hth
  have hT0 := hT
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hE, hTy, htv, hi, -, -⟩ := hT0
  obtain ⟨cl, hcl, -⟩ := publish_own_cellB hTy.1 (finv_ofB htv hi) hterm hea hws
  have hsx : E.sto x ≠ none := by
    rw [← hCE, ← hx]
    show η.sto ad.label ≠ none
    rw [hcl]; exact Option.some_ne_none _
  rw [bornBit_some hsx] at hle
  exact ⟨th1, E, Tot, HP, hth1, hT, hm, hP, hb, hn, hsx, by omega, hX, hA, hTyE, hRc, fun h1 => absurd h1 (by decide), hR⟩

/-- **(ownXLe_born) `OFresh` holds** at a `SysInvN` window start (the former temporary `oFresh`). -/
theorem oFresh_of {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hps : TermScope.ProgScopeOK p = true) {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {S : AllocLabel → Prop} (hinv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hth : c.ths[i]? = some th)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hrs : TermScope.RunScope c) (hvI : TermViewInv.ViewInv c) (hK : FlatAnchor.ContB c.lbase c.n i p th (Cut Eg i S)) :
    OFresh p k arch i c th := by
  intro c1 th1 y a e rt ws ad j hsolo hc1 hth1 hterm hea hws hj hjl
  have hPS := TermMain.pwSkel_ok
  have hSub := TermMain.pwSubS_ok
  have hSig := TermMain.pwSig_ok
  have hTA := TermMain.tidAt_cut hinv i S
  have hQ := TermCertScope.Flat.scopeAtB_solo (i := i) (k := k) (arch := arch) hps hrs
  have h0 := ownXLeBU_start hinv hth hS hj hK
  have h1 := ownXLe_runAllSU hP hPS hSub hSig hQ hvI h0 hTA hsolo hc1
  have h2 := ownXLeB_of_U h1 hth1 hterm hea hws hjl
  exact eta_oracle hP hPS hSub hSig (fun c0 h hc => hQ c0 (solo_trans hsolo h) hc)
    (TermViewInv.viewInv_solo hvI hsolo) (by rw [hjl]; exact h2) (TermTyped.tidAt_solo hsolo hTA) (.refl _) hth1 hterm hea hws hinv.rle

end CertWinProof
