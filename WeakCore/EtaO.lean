import WeakCore.EtaN
import WeakCore.ShadowWinChain
import WeakCore.WrIniInst
import WeakCore.WinPubSplit
/-! **EtaO** (B11/B12 on (R′)): the oracle `hO` of `noHold_eta` in the NON-fresh case, from the window
ownership chain: ShadowWinChain `ownXLe_pub_chainS` (seeded by `OwnXLeB … x 1 c`, e.g. WinStart `ownXLeB_start`),
`OwnXLeB.rf_zero` and `not_bufInitL_ofB`. Before the publish step the term is still the publish, so
`BufInitL` fails syntactically. -/
namespace CertWinProof
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat
  TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat
  TermOwnK3.Flat TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem not_bufInitL_pub {th : TTh} {y : String} {a : At} {e : Expr} {l : AllocLabel}
    (hterm : th.term = .let_ y (.publish a) e) : ¬ BufInitL th l := by
  rintro ⟨x1, bb, ib, v, e1, rt, ws, ad, h1, -, -, -⟩
  rw [hterm] at h1
  cases h1

theorem eta_oracle [WrIniCB] {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {k : Promises.Knobs}
    {arch : Arch} {E0 : TEnv} {i : Nat} {c c1 : Cfg} {th1 : TTh} {y : String} {a : At} {e : Expr}
    {rt : Ty} {ws : List Word} {ad : Address} (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAtB p i c0) (hvI : TermViewInv.ViewInv c)
    (h0 : OwnXLeB p k arch E0 i ad.label 1 c) (hTA : TermTyped.TidAt i c E0) (hsolo : Solo p k arch i c c1)
    (hth1 : c1.ths[i]? = some th1) (hterm : th1.term = .let_ y (.publish a) e)
    (hea : evalAt th1.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad 0])
    (hR0 : ∀ l, E0.rini l ≤ E0.ini l) :
    ∀ c0, Solo p k arch i c1 c0 → Certified p k arch c0 i → ∀ th, c0.ths[i]? = some th →
      ¬ BufInitL th ad.label := by
  intro c0 h2 hc0 th hth
  rcases FlatWinStart.solo_pub_split h2 hth1 hterm with ⟨tha, h1, h3, -⟩ |
    ⟨c1p, thp, c1', h1, h3, h4, h5, h6, h7⟩
  · have hee : tha = th := Option.some.inj (h1.symm.trans hth)
    rw [← hee]
    exact not_bufInitL_pub (h3.trans hterm)
  · have hea' : evalAt thp.env a = some (rt, ws) := by rw [h5]; exact hea
    obtain ⟨η1, -, -, -, -, -, hI⟩ := ownXLe_pub_chainS hP hPS hSub hSig hQ hvI h0 hTA
      (solo_trans hsolo h1) h6 h3 (h4.trans hterm) hea' hws rfl h7 hc0 hR0
    obtain ⟨th', hth', ρ, η, cx, Rf, Rs, hE, hTy, hFI, hz⟩ := OwnXLeB.rf_zero hI
    have hee : th' = th := Option.some.inj (hth'.symm.trans hth)
    rw [← hee]
    exact not_bufInitL_ofB hE hTy hFI hz

end CertWinProof
