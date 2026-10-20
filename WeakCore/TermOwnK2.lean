import WeakCore.TermOwnX2
import WeakCore.TermPubW
import WeakCore.TermOwnHeldQ

/-!
# TermOwnK2 (own-key layer, package): own-cell loads/stores/xchg

Package K2 of `OwnXStepPkg` (`opPkg = 2`): `load`, `store`, `xchg`, `loadAt`, `loadAtF`.

Route (b), trimmed copies: each per-variant lemma `k2_*` is a copy of the corresponding
`TermStep.tstepMR_*`/`tstepMC_*` body with the
full-holding/credit/`Sp`/`SeenKeep`/`BoxNewV` lines deleted and the private holding (`MemHeldP`)
carried by the `TermOwnHeldQ` helpers.  Conclusion: `TermOwnHeldQ.StepC` (key total at `z` bounded).
-/

namespace TermOwnK2
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Shared tails (new) -/

/-- A resource-free step at `CE η` keeping memory and promises (every load). -/
theorem stepC_keep {p : Prog} {g : G} {η : TEnv} {th th1 : TTh} {s s' : St} {Rf Rs HP : Res} {z : AllocLabel}
    (hT : ThInvRE p (CE η) (withS th1 s') (Rf + Rs)) (hm : MemInv g (CE η) s')
    (hH : MemHeldP (CE η) s HP) (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises)
    (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) : StepC p g z (CE η) s th (Rf + Rs) HP (s'.mem, s'.pairs, withS th1 s') :=
  ⟨CE η, Rf + Rs, HP, hT, hm, memHeldOn_eqs hH e1 e2, hni, hx, Nat.le_refl _, anchStep_eqs e1 e2⟩

/-- **A store keeps the private holding up to the stored resources `D`**: off a private target the
holding is unchanged; at a private target its entry `R0` becomes an `R2 ≤ R0 + D` (own keys). -/
theorem privStore {E : TEnv} {s s' : St} {HP D : Res} {k : Promises.Knobs} {arch : Arch} {pw : Word}
    {a : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hH : MemHeldP E s HP) (hpl : PromLt s) (hs : s' ∈ storeUnits k arch pw a rel us ws 0 s)
    (hent : Priv E a.label → ∀ R0, HeldEntry E s a.label R0 →
      ∃ R2, HeldEntry E s' a.label R2 ∧ ∀ y : Nat, R2 (.own y) ≤ R0 (.own y) + D (.own y)) :
    ∃ HP', MemHeldP E s' HP' ∧ ∀ y : Nat, HP' (.own y) ≤ HP (.own y) + D (.own y) := by
  by_cases hq : Priv E a.label
  · obtain ⟨R0, H0, rfl, he, hX⟩ := memHeldOn_focus hH hq
    obtain ⟨R2, he2, hle⟩ := hent hq R0 he
    refine ⟨R2 + H0, memHeldOn_unfocus (memHeldOn_store hX (fun l h => h.2) hpl hs) he2 hq, fun y => ?_⟩
    have := hle y
    simp only [Res.add_apply]; omega
  · exact ⟨HP, memHeldOn_store hH (fun l h e => hq (e ▸ h)) hpl hs, fun y => Nat.le_add_right _ _⟩

/-- **The generic tail at `CE η`**: the frame went from `Rf` to `Rr`, giving up `D` at own key `z`, and
the private holding grew by at most `D` (own keys). -/
theorem stepC_own {p : Prog} {g : G} {η : TEnv} {r : Memory × List Ts × TTh} {Rf Rs Rr D HP : Res}
    {z : AllocLabel} {th : TTh} {s : St} (hnb : ∀ E1, BumpIf th E1) (hT : ThInvRE p (CE η) r.2.2 (Rr + Rs)) (hm : MemInv g (CE η) (stOf r.1 r.2.1 r.2.2))
    (hH : ∃ HP', MemHeldP (CE η) (stOf r.1 r.2.1 r.2.2) HP' ∧ ∀ y : Nat, HP' (.own y) ≤ HP (.own y) + D (.own y))
    (hle : D (.own z) + Rr (.own z) ≤ Rf (.own z)) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) :
    StepC p g z (CE η) s th (Rf + Rs) HP r := by
  obtain ⟨HP', hH', hle'⟩ := hH
  refine ⟨CE η, Rr + Rs, HP', hT, hm, hH', hni, hx, ?_, anchStep_same hnb⟩
  have h2 := hle' z
  simp only [Res.add_apply]
  omega

/-- `Rv + Rr ≤ Rf` at an own key. -/
theorem own_le {Rv Rr Rf : Res} (h : Rv + Rr ≤ Rf) (z : Nat) : Rv (.own z) + Rr (.own z) ≤ Rf (.own z) := by
  have := Res.le_def.1 h (.own z); simp only [Res.add_apply] at this; exact this

/-! ## Loads -/

-- copied from TermStep.tstepMR_loadOwn
theorem k2_loadOwn {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u)) (hnw : wordOf (Ty.ptr .own u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadPub hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadOwn hp _ hc haf hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.own, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hnwc : wordOf (close th.σs (.ptr .own u)) = none := by
    rw [close_ptr]; exact wordOf_ptr_of_wordFree (wordFree_close hi0.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_view hi0 hpk htv (bind_opaqueOK hb)
  have hwr : wordOf (Ty.ptr .own ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [close_ptr, hX] at hnwc; simp [wordOf] at hnwc
    | _ => rfl
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h =>
    hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, -, hld, -⟩ := ownLoad (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VR η hcty).1) hna hsku (peek_cell_lyt hi0.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl (bind_opaqueOK hb) hea rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key]
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  have hvz : VRR ρ η u (shp ru) wsr .zero := VR_VRR_copy_finv hi0 hE haf htb hvr
  have hfr := bindR hb hi (RLink_of hE.2.1 hE.2.2) hvz hlay
  rw [Res.add_zero] at hfr
  exact stepC_keep ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    (MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl)) hH f1 f4 hni hx

-- copied from TermStep.tstepMR_loadLoc
theorem k2_loadLoc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u)) (hnw : wordOf (Ty.loc .own u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadPub hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadOwn hp _ hc haf hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.own, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VR hi0.2.1 hpk
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u) := fun n e hF => by
    have := Fd_arrFree hF haf'; simp [Ty.arrFree] at this
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_target (rfl : cellOf (.loc .own u) = some (.own, u)) hnb hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .own ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hwf := wordFree_close hi0.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf)
  have hwr : wordOf (Ty.loc μr ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [hX] at hwf; simp [Ty.wordFree, Ty.wordFreeIn] at hwf
    | _ => rfl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact sig_WitL hi0.2.2.2.1 ρ (bind_opaqueOK hb) (lt_of_guardT htb hi0.2.2.2.2.1)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := locLoad (arch := g.arch) (pw := pw) (acq := acq)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (cell_lyt hl.2.2.2.2 rfl rfl).2
        (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 (bind_opaqueOK hb) htb (cell_lyt hl.2.2.2.2 rfl rfl).2)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  have hvz : VRR ρ η u (shp ru) wsr .zero := VR_VRR_copy_finv hi0 hE haf htb hvr
  have hfr := bindR hb hi (RLink_of hE.2.1 hE.2.2) hvz hlay
  rw [Res.add_zero] at hfr
  refine stepC_keep ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    (MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')) hH f1 f4 hni hx

-- copied from TermStep.tstepMR_loadAt
theorem k2_loadAt {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.loadAt b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadAt hp hbuf hint hlt hltk haf hb =>
  obtain ⟨t, u, n, k, j, hp, hbuf, hint, hlt, hltk, haf, hb⟩ : ∃ t u n k j, cx.peek b = .ok t ∧
      bufOf t = some (.own, n, u, k) ∧ IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      affine cx.ke u = false ∧ cx.bind x u = .ok c' :=
    ⟨_, _, _, _, _, hp, hbuf, hint, hlt, hltk, haf, hb⟩
  have hi0 := hi.1
  obtain ⟨rt, w, ad, c, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hmode, hini, hsku, hsig, htbS, -⟩ :=
    slot_view hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk (bind_opaqueOK hb)
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoad (ad := offs ad (ev ρ j * nWords us)) (arch := g.arch) (pw := w) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2
        (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 (bind_opaqueOK hb) htbS (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2)
  rw [hus] at hus'; cases hus'
  have key : tstep g mem pairs th =
      (loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ur, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hj, addrOf, hwv, hbe, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  have htb : tb cx.ke.length u = true := tb_bufOf (peek_tb htv hp) hbuf
  have hvz : VRR ρ η u (shp ur) wsr .zero := VR_VRR_copy_finv hi0 hE haf htb hvr
  have hfr := bindR hb hi (RLink_of hE.2.1 hE.2.2) hvz hlay
  rw [Res.add_zero] at hfr
  refine stepC_keep ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    (MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')) hH f1 f4 hni hx

-- copied from TermStep.tstepMR_loadAtF
theorem k2_loadAtF {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {q : List Nat} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.loadAtF b i q) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadAtF hp hbuf hct hop hint hlt hltk haf hb =>
  obtain ⟨t, u, c, n, k, j, hp, hbuf, hct, hop, hint, hlt, hltk, haf, hb⟩ : ∃ t u c n k j, cx.peek b = .ok t ∧
      bufOf t = some (.own, n, u, k) ∧ compTy u q = some c ∧ cx.opaqueOK u = true ∧ IntIdx cx i j ∧
      LtI cx j n ∧ LtI cx j k ∧ affine cx.ke c = false ∧ cx.bind x c = .ok c' :=
    ⟨_, _, _, _, _, _, hp, hbuf, hct, hop, hint, hlt, hltk, haf, hb⟩
  have hi0 := hi.1
  obtain ⟨rt, w, ad, cc, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hmode, -, hsku, hsig, htbS, hiniF⟩ :=
    slot_view hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
  obtain ⟨cR, o, hco, hskc, hsgc, -, hato⟩ := compOff_rt q u c ur us hct hsku hsig hus
  have haf' : (cl ρ η.wit 0 0 c).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af c 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 c ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hat' : AtOff cc.ty (offs ad (ev ρ j * nWords us + o)).offset (cl ρ η.wit 0 0 c) := by
    have h2 := AtOff_trans hat hato
    simpa [offs, Nat.add_assoc] using h2
  obtain ⟨cs, hcs, ⟨r0, hr0⟩, hld, hstw⟩ := locLoad (ad := offs ad (ev ρ j * nWords us + o)) (arch := g.arch) (pw := w)
    (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat' (hiniF o _ hato) hna hskc hsgc
      (compOff_lyt q u c ur cR o hct hsku (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2 hco)
        (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 (bind_opaqueOK hb) (tb_compTy q u c hct htbS) (compOff_lyt q u c ur cR o hct hsku (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2 hco))
  have key : tstep g mem pairs th =
      (loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, cR, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hj, addrOf, hwv, hbe, hus, hco, hcs, List.map_map]; rfl
  rw [key] at ⊢
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  have htb : tb cx.ke.length c = true := tb_compTy q u c hct (tb_bufOf (peek_tb htv hp) hbuf)
  have hvz : VRR ρ η c (shp cR) wsr .zero := VR_VRR_copy_finv hi0 hE haf htb hvr
  have hfr := bindR hb hi (RLink_of hE.2.1 hE.2.2) hvz hlay
  rw [Res.add_zero] at hfr
  refine stepC_keep ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    (MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')) hH f1 f4 hni hx

-- copied from TermStep.tstepMR_loadPub
theorem k2_loadPub {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadOwn hp _ hc _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadPub hp _ hc haf _ hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.pub, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hnwc : wordOf (close th.σs (.ptr .pub u)) = none := by
    rw [close_ptr]; exact wordOf_ptr_of_wordFree (wordFree_close hi0.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf))
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, hne, hld, hstw⟩ :=
    loadPub_core (p := p) (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk (bind_opaqueOK hb) hi0 hE htv hm
  have hwr : wordOf (Ty.ptr .pub ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [close_ptr, hX] at hnwc; simp [wordOf] at hnwc
    | _ => rfl
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, hlay', hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨f1, -, f3, -⟩ := loadUnits_frame us 0 _ (s', wsr) hl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .pub u) = some (.pub, u))
  have hvz : VRR ρ η u (shp ru) wsr .zero := VR_VRR_copy_finv hi0 hE haf htb hvr
  have hfr := bindR hb hi (RLink_of hE.2.1 hE.2.2) hvz hlay'
  rw [Res.add_zero] at hfr
  exact stepC_keep ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    hm' hH f1 f3 hni hx

-- copied from TermStep.tstepMR_loadPubLoc
theorem k2_loadPubLoc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have hi0 := hi.1
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadOwn hp _ hc _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadPub hp _ hc haf _ hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.pub, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VR hi0.2.1 hpk
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u) := fun n e hF => by
    have := Fd_arrFree hF haf'; simp [Ty.arrFree] at this
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_target (rfl : cellOf (.loc .pub u) = some (.pub, u)) hnb hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .pub ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hwf := wordFree_close hi0.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf)
  have hwr : wordOf (Ty.loc μr ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [hX] at hwf; simp [Ty.wordFree, Ty.wordFreeIn] at hwf
    | _ => rfl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .pub u) = some (.pub, u))
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact sig_WitL hi0.2.2.2.1 ρ (bind_opaqueOK hb) (lt_of_guardT htb hi0.2.2.2.2.1)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  by_cases hown : c.owner = some η.tid
  · -- the thread's own cell: an own load
    obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadI (arch := g.arch) (pw := pw) (acq := acq)
      (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.1 hsto hown hat hini hna
      (fun _ f hf hns => by
        simp only [ModeOK] at hmode
        obtain ⟨f0, hf0, hsf⟩ := hmode
        obtain rfl : f0 = f := Option.some.inj (hf0.symm.trans hf)
        rcases hsf with hs | hs
        · exact absurd hs hns
        · exact hs pw (by simp)) hsku hsig
        (cell_lyt hl.2.2.2.2 rfl rfl).2
          (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 (bind_opaqueOK hb) htb (cell_lyt hl.2.2.2.2 rfl rfl).2)
    have key : tstep g mem pairs th =
        (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
    rw [key] at ⊢
    intro r hr hpr0
    rw [List.mem_map] at hr
    obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
    obtain ⟨hvr, hlay', f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
    have hvz := VR_VRR_copy_finv hi0 hE haf htb hvr
    have hfr := bindR hb hi (RLink_of hE.2.1 hE.2.2) hvz hlay'
    rw [Res.add_zero] at hfr
    exact stepC_keep ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
      (MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')) hH f1 f4 hni hx
  · -- another thread's cell
    simp only [ModeOK] at hmode
    obtain ⟨f, hf, hsf⟩ := hmode
    have hfv : f ≤ pw.view := by
      rcases hsf with hs | hs
      · rcases hm.2.2.2.2.2.2.2.2.1.1 ad.label hs with ⟨c0, h1, h2⟩ | ⟨h1, -⟩
        · refine absurd ?_ hown
          have h1' : η.sto ad.label = some c0 := h1
          rw [hsto] at h1'
          rw [Option.some.inj h1']; exact h2
        · have h1' : η.sto ad.label = none := h1
          rw [hsto] at h1'; cases h1'
      · exact hs pw (by simp)
    have hlU : accs (cl ρ η.wit 0 0 u) ≠ none := by
      rcases AtOff_lay hat with h | ⟨N, e', h, -⟩
      · exact h
      · exact absurd h (hna N e')
    have hlr := pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl (bind_opaqueOK hb) hea rfl
    obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := Option.ne_none_iff_exists'.1 (by rw [hlr]; exact hlU)
    have husU : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr, hus]
    have key : tstep g mem pairs th =
        (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
    rw [key] at ⊢
    obtain ⟨⟨r0, hr0⟩, hval, hsv⟩ := pubLoadAt (arch := g.arch) (pw := pw) (acq := acq)
      hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.2.1 hsto hown hf hfv hat hini hna husU
    intro r hr hpr0
    rw [List.mem_map] at hr
    obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
    obtain ⟨q, hq, hle⟩ := hval (s', wsr) hl' (hpr0)
    have hrl : wsr.length = nWords us := (Reads_unit us 0 wsr (loadUnits_reads us 0 _ (s', wsr) hl' [] (fun _ _ h => by cases h))).1
    obtain ⟨f1, f2, f3, f4⟩ := loadUnits_frame us 0 _ (s', wsr) hl'
    obtain ⟨hvr0, hV0⟩ := ValOf.env hq
    have hvr : VR ρ η u (shp ru) wsr := by
      rw [shp_of_sig hsig]
      exact (VR_close hE.2.1 ρ u [] 0 ρ (fun _ => 0) (shp (cl ρ η.wit 0 0 u)) wsr (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).2 (VR_up _ _ q wsr hle hvr0)
    have hlay' : Lay th.σs u ru wsr :=
      ⟨fun us' h => by rw [hus] at h; cases h; exact hrl, hsku, by simp [wc, hus],
        Valid_of_sig hsig.symm (Valid_vals _ q wsr hle.vals hV0), (cell_lyt hl.2.2.2.2 rfl rfl).2⟩
    have hvz := VR_VRR_copy_finv hi0 hE haf htb hvr
    have hfr := bindR hb hi (RLink_of hE.2.1 hE.2.2) hvz hlay'
    rw [Res.add_zero] at hfr
    refine stepC_keep ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
      ?_ hH f1 f3 hni hx
    refine MemInv_loadF hm f1 f2 (fun l c1 hc1 ho1 o => loadUnits_cohF us 0 _ (s', wsr) hl' ⟨l, o⟩ ?_)
      f3 f4 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')
      (fun l B hB o => loadUnits_cohF us 0 _ (s', wsr) hl' ⟨l, o⟩ (fun he => by
        have h0 := (hm.2.2.2.2.2.2.2.2.2.1.2.2 l B hB).1
        have hl0 : l = ad.label := he
        rw [hl0] at h0; have h1 : η.sto ad.label = none := h0; rw [hsto] at h1; cases h1))
    intro hle'
    have hl'' : l = ad.label := hle'
    have h1 : η.sto l = some c1 := hc1
    rw [hl'', hsto] at h1
    exact hown (by rw [Option.some.inj h1]; exact ho1)

-- copied from TermStep.tstepMC_loadWordOwn
theorem k2_loadWordOwn {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {r : Idx} {P : Proto}
    {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own (.word r P)))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ :=
    ownPtr_view hi0 hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, ⟨ro, hro⟩, hld, hstw⟩ := ownLoad (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VR η hcty).1) hna hsku
    (peek_cell_lyt hi0.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl)
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  obtain ⟨w, n, rfl, hvr'⟩ := word_bind hg hvr
  have hfr := bindR0 hb (pushR x n hi) hvr' (Lay_int w rfl) trivial
  exact stepC_keep ⟨vcons n ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    ((MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl))) hH f1 f4 hni hx

-- copied from TermStep.tstepMC_loadWordPub
theorem k2_loadWordPub {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {r : Idx} {P : Proto}
    {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub (.word r P)))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, hne, hld, hstw⟩ :=
    loadPub_core (p := p) (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk
      (by simp [Cx.opaqueOK, Ty.guardT]) hi0 hE htv hm
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨f1, -, f3, -⟩ := loadUnits_frame us 0 _ (s', wsr) hl
  obtain ⟨w, n, rfl, hvr'⟩ := word_bind hg hvr
  have hfr := bindR0 hb (pushR x n hi) hvr' (Lay_int w rfl) trivial
  exact stepC_keep ⟨vcons n ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    hm' hH f1 f3 hni hx

-- copied from TermStep.tstepMC_loadWordLoc
theorem k2_loadWordLoc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {μ : Mode} {r : Idx} {P : Proto}
    {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  have hg' : P.ghost = false := hg
  have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg']
  obtain ⟨ad, pw, μr, ru, hea, haddr, hus, hsku, -, hne, hld, -, hstw⟩ :=
    locCell (acq := acq) (rel := false) (g := g) (mem := mem) (pairs := pairs)
      hpk hμ (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi0 hE htv hm
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, haddr, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨f1, -, f3, -⟩ := loadUnits_frame [.one] 0 _ (s', wsr) hl
  obtain ⟨w, n, rfl, hvr'⟩ := word_bind hg' hvr
  have hfr := bindR0 hb (pushR x n hi) hvr' (Lay_int w rfl) trivial
  exact stepC_keep ⟨vcons n ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    hm' hH f1 f3 hni hx


/-! ## Stores -/

-- copied from TermStep.tstepMR_storeOwn
theorem k2_storeOwn {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u)) (hnw : wordOf (Ty.ptr .own u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storePub hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeOwn hp _ hc hwf hu hsub hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.own, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_view hi0 hpk htv ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have husA : accs c.ty = some us := ((Fd_lay hcty).2.2.1.trans (pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords us) := by rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  replace hval := (Fd_EnvVal (CE η) hcty).2 hval
  have hvalR : EnvValR (CE η) c.ty wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRR ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_sub hsat hsub _ _ _ hvrv
    have hvc : VRR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_close hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    refine ⟨?_, hval.2⟩
    rw [(Fd_lay hcty).1]
    exact (Fd_VRR η hcty).2 hvc
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hsn := hm.2.2.2.2.1
  have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  refine stepC_own (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩ (MemInv_store hm hsto hown husA hval hlen s' hs')
    (privStore hH hm.2.2.1 hs' fun hq R0 _ => ?_) (own_le hle z) hni hx
  obtain ⟨g2, -⟩ := storeUnits_latP (a := ⟨lab, 0⟩) us wsv 0 (stOf mem pairs th)
    (stOf mem pairs th).vs.vRelSt hm.2.2.1 (MemInv_nodup hm) (Nat.le_refl _) s' hs'
  have htail : ∀ j : Nat, j < nWords us → TailP (stOf mem pairs th) (offs ⟨lab, 0⟩ (0 + j)) := fun j hj => by
    have := OwnOKPF_tail hm.2.1 hsto hown hq.2 hus' j hj
    simpa [offs] using this
  exact ⟨Rv, HeldEntry_ownN hsto (NVP_store (NVP_priv hq) hm.2.2.1 hs') (storeOwn_latestP hlen (g2 htail))
    (Or.inl ⟨by rw [hus', List.length_map, hlen], hvalR.store hsn⟩), fun y => Nat.le_add_left _ _⟩

-- copied from TermStep.tstepMR_storeLoc
theorem k2_storeLoc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u)) (hnw : wordOf (Ty.loc .own u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storePub hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeOwn hp _ hc hwf hu hsub hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.own, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => hwcu (by rw [h]; simp [wc, accs])
  obtain ⟨ad, c, pw, μr, ru, hea, hpw, hsto, hat, hini, hown, hsku, hsig⟩ := locView hi0 hpk htv ho hwcu
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_cell_lyt hi0.2.1 hpk hea rfl rfl).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValR hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  refine stepC_own (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    (MemInv_storeAt hm hsto hown hat hini hna hval hwUA hlen s' hs') ?_ (own_le hle z) hni hx
  by_cases hq : Priv (CE η) ad.label
  · obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput⟩ := heldStoreAtP hm hH hq hsto hown (NVP_priv hq)
      (OwnOKPF_cellP hm.2.1 hsto hown hq.2) hat hini hna hvalR hwU hlen
    refine ⟨R2 + H0, hput g.k g.arch pw rel _ rfl rfl (LoadCoh_of_eq hm.2.1 rfl) (fun _ => Nat.le_refl _)
      hm.2.2.2.2.1 s' hs', fun y => ?_⟩
    have h2 := congrArg (fun R : Res => R (.own y)) hRe
    simp only [Res.add_apply] at h2 ⊢; omega
  · exact ⟨HP, memHeldOn_store hH (fun l h e => hq (e ▸ h)) hm.2.2.1 hs', fun y => Nat.le_add_right _ _⟩

-- copied from TermStep.tstepMR_storePub
theorem k2_storePub {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.pub, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .pub u) = some (.pub, u))
  obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, hacc, hsku, hsig⟩ := pubPtr_view hi0 hpk htv ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hlr : accs ru = accs c.ty := by
    rw [(Fd_lay hcty).2.2.1]
    exact pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    cases h : accs ru with
    | none => rw [h] at hlr; exact absurd hlr.symm hacc
    | some us => exact ⟨us, rfl⟩
  have husc : accs c.ty = some us := by rw [← hlr, hus]
  have hus' : wc c.ty = some (nWords us) := by simp [wc, husc]
  have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  replace hval := (Fd_EnvVal (CE η) hcty).2 hval
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hvalR : EnvValR (CE η) c.ty wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRR ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_sub hsat hsub _ _ _ hvrv
    have hvc : VRR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_close hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    refine ⟨?_, hval.2⟩
    rw [(Fd_lay hcty).1]
    exact (Fd_VRR η hcty).2 hvc
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hsn := hm.2.2.2.2.1
  have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  by_cases hown : c.owner = some η.tid
  · refine stepC_own (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩ (MemInv_storeF hm hsto hown husc hval hlen s' hs')
      (privStore hH hm.2.2.1 hs' fun hq R0 _ => ?_) (own_le hle z) hni hx
    obtain ⟨g2, -⟩ := storeUnits_latP (a := ⟨lab, 0⟩) us wsv 0 (stOf mem pairs th)
      (stOf mem pairs th).vs.vRelSt hm.2.2.1 (MemInv_nodup hm) (Nat.le_refl _) s' hs'
    have htail : ∀ j : Nat, j < nWords us → TailP (stOf mem pairs th) (offs ⟨lab, 0⟩ (0 + j)) := fun j hj => by
      have := OwnOKPF_tail hm.2.1 hsto hown hq.2 hus' j hj
      simpa [offs] using this
    exact ⟨Rv, HeldEntry_ownN hsto (NVP_store (NVP_priv hq) hm.2.2.1 hs') (storeOwn_latestP hlen (g2 htail))
      (Or.inl ⟨by rw [hus', List.length_map, hlen], hvalR.store hsn⟩), fun y => Nat.le_add_left _ _⟩
  · refine stepC_own (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
      (MemInv_storePubAt (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
        (IniAt_of_ne fun N e he => hna N e he) hna hval husc hlen s' hs')
      ⟨HP, memHeldOn_store hH (fun l h e => ?_) hm.2.2.1 hs', fun y => Nat.le_add_right _ _⟩ (own_le hle z) hni hx
    obtain ⟨⟨c2, h2, ho⟩, -⟩ := h
    have h3 : η.sto lab = some c2 := by rw [e] at h2; exact h2
    rw [hsto] at h3; cases h3; exact hown ho

-- copied from TermStep.tstepMR_storePubLoc
theorem k2_storePubLoc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.pub, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .pub u) = some (.pub, u))
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => hwcu (by rw [h]; simp [wc, accs])
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VR hi0.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_target (rfl : cellOf (.loc .pub u) = some (.pub, u)) (Fd_noarr fun h => hwcu (by simp [wc, h])) hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .pub ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact hsigu
  have hlr := pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  have husU : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr, hus]
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := hlr.symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValR hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  simp only [ModeOK] at hmode
  obtain ⟨f, hf, -⟩ := hmode
  refine stepC_own (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    (by by_cases hown : c.owner = some η.tid
        · exact MemInv_storeAtI hm hsto hown hat hini hna hval hwUA hlen s' hs'
        · exact MemInv_storePubAt hm hsto hown hf hat hini hna hval husU hlen s' hs')
    ⟨HP, memHeldOn_store hH (fun l h e => ?_) hm.2.2.1 hs', fun y => Nat.le_add_right _ _⟩ (own_le hle z) hni hx
  have h3 : η.pfr ad.label = none := by rw [← e]; exact h.2
  rw [hf] at h3; cases h3

/-! ## Exchanges -/

/-- **The old value of an own cell with a frontier is own-free**: its static-type reading `VR` has
resources (`noIallV`, from `StoNIE`) with zero own keys (frontier cells are own-free, `MemInv_noOwnT`). -/
theorem oldFree {ρ : Nat → Nat} {η : TEnv} {u ru T : Ty} {ws : List Word} (hco : Coh η) (hcr : CohR η)
    (hTU : ∀ S ws, VR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) S ws → VR (fun _ => 0) (CE η) T S ws)
    (hUT : ∀ S ws R, VRR (fun _ => 0) (CE η) T S ws R → VRR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) S ws R)
    (hni : noIallV T = true) (hno : Ty.noOwnIn [] T = true) (hv : VR ρ η u (shp ru) ws) :
    ∃ R, VRR ρ η u (shp ru) ws R ∧ ∀ y : Nat, R (.own y) = 0 := by
  have h2 := (VR_close hco ρ u [] 0 ρ (fun _ => 0) (shp ru) ws (fun k => rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hv
  obtain ⟨R, hR⟩ := VR_VRR T hni (RInv_CE η) (hTU _ _ h2)
  exact ⟨R, (VRR_close hco hcr ρ u [] 0 ρ (fun _ => 0) (shp ru) ws R (fun k => rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero _))).2 (hUT _ _ _ hR),
    fun y => TermBlkZ.VRR_own_zero y T [] (CE η) _ _ _ R hno (fun _ _ _ _ h => h.elim) (fun _ _ _ _ h => h.elim) hR⟩

-- copied from TermStep.tstepMR_xchgOwn
theorem k2_xchgOwn {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.xchg a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hxz : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, u', o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t u' o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t u' o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv u' ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok c' := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_view hi0 hpk htv ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h =>
    hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, -, hld, -⟩ := ownLoad (arch := g.arch) (pw := pw) (acq := false) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VR η hcty).1) hna hsku (peek_cell_lyt hi0.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl)
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have husA : accs c.ty = some us := ((Fd_lay hcty).2.2.1.trans (pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords us) := by rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  replace hval := (Fd_EnvVal (CE η) hcty).2 hval
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hvalR : EnvValR (CE η) c.ty wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRR ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_sub hsat hsub _ _ _ hvrv
    have hvc : VRR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_close hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    refine ⟨?_, hval.2⟩
    rw [(Fd_lay hcty).1]
    exact (Fd_VRR η hcty).2 hvc
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ⟨lab, 0⟩ false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key] at ⊢
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw ⟨lab, 0⟩ false us 0 (stOf mem pairs th) → PromAbove r1.1 → MemInv g (CE η) r1.1 :=
    fun r1 h hp => by
      obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
      exact MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  intro r hr hpr
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hvr, hlay, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  by_cases hq : Priv (CE η) lab
  · have hnv := NVP_priv (s := stOf mem pairs th) hq
    obtain ⟨vals, hcell, hlat⟩ := OwnOKPF_cellP hm.2.1 hsto hown hq.2
    have hwc := (hcell.plain (notArr_of_wc hus')).1
    obtain ⟨vals', hWv, hP'⟩ := own_msgWordsN (E := CE η) hnv vals hlat
    have hl' : vals'.length = nWords us := by
      rw [← hWv.length]; rw [hus'] at hwc; exact (Option.some.inj hwc).symm
    obtain ⟨R0, H0, rfl, hent0, hX⟩ := memHeldOn_focus hH hq
    have hvR0 : ValOfR (CE η) c.ty vals' R0 :=
      HeldEntry_vals hent0 hsto hna (by rw [hus', hl']) (fun o w h => (hP' o w h).2)
    have hWold : WLe vals' old := (loadUnits_latestPA hl'
      (fun j w hj => by simpa [offs] using (hP' j w hj).1) h1 hp1).1
    have hvold : VRR ρ η u (shp ru) old R0 := by
      have h1 := VRR_up _ _ _ _ _ hWold hvR0.1
      have h2 : VRR (fun _ => 0) (CE η) c.ty (shp c.ty) old R0 :=
        VRR_mono c.ty (CE (CE η).unsee) (CE η) _ _ _ _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) rfl rfl rfl (fun _ _ h => h)
          (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h.elim) (fun _ _ h => h) h1
      have h3 := (Fd_VRR η hcty).1 h2
      rw [(Fd_lay hcty).1, ← shp_of_sig hsig] at h3
      exact (VRR_close hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp ru) old R0 (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).2 h3
    obtain ⟨g2, -⟩ := storeUnits_latP (a := ⟨lab, 0⟩) us wsv 0 s1 s1.vs.vRelSt hm1'.2.2.1
      hm1'.2.2.2.2.2.2.2.2.2.2.1 (Nat.le_refl _) s2 hs2
    have htail : ∀ j : Nat, j < nWords us → TailP s1 (offs ⟨lab, 0⟩ (0 + j)) := fun j hj => by
      have := cellP_tailLoad (OwnOKPF_cellP hm.2.1 hsto hown hq.2) fc (loadUnits_cohMono us 0 _ _ h1) f1 f3
        hsto hown hus' j hj
      simpa [offs] using this
    have hent : HeldEntry (CE η) s2 lab Rv := HeldEntry_ownN hsto (NVP_store (NVP_eqs hnv f1 f3) hm1'.2.2.1 hs2)
      (storeOwn_latestP hlen (g2 htail))
      (Or.inl ⟨by rw [hus', List.length_map, hlen], hvalR.store hm1'.2.2.2.2.1⟩)
    have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvold hlay
    refine ⟨CE η, Rr + R0 + Rs, Rv + H0, ⟨ρ, η, c', Rr + R0, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      MemInv_store hm1' hsto hown husA hval hlen s2 hs2,
      memHeldOn_unfocus (memHeldOn_store (memHeldOn_eqs hX f1 f3) (fun l h => h.2) hm1'.2.2.1 hs2) hent hq, hni, hxz, ?_, anchStep_same (bumpIf_nb hterm)⟩
    have h1 := own_le hle z
    simp only [Res.add_apply]; omega
  · obtain ⟨f, hf⟩ : ∃ f, (CE η).pfr lab = some f := by
      cases h : (CE η).pfr lab with
      | none => exact absurd ⟨⟨c, hsto, hown⟩, h⟩ hq
      | some f => exact ⟨f, rfl⟩
    obtain ⟨R1, hvold, hz⟩ := oldFree (T := c.ty) hE.2.1 hE.2.2 (fun S ws => (Fd_VR η hcty).2) (fun S ws R => (Fd_VRR η hcty).1)
      (hni lab c hsto) (MemInv_noOwnT hm hsto hf) hvr
    have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvold hlay
    refine ⟨CE η, Rr + R1 + Rs, HP, ⟨ρ, η, c', Rr + R1, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      MemInv_store hm1' hsto hown husA hval hlen s2 hs2,
      memHeldOn_store (memHeldOn_eqs hH f1 f3) (fun l h e => hq (by rw [e] at h; exact h)) hm1'.2.2.1 hs2, hni, hxz, ?_, anchStep_same (bumpIf_nb hterm)⟩
    have h1 := own_le hle z
    have h2 := hz z
    simp only [Res.add_apply]; omega

-- copied from TermStep.tstepMR_xchgLoc
theorem k2_xchgLoc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.xchg a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hxz : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, u', o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t u' o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t u' o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv u' ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok c' := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig (sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1))]
    exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨ad, c, pw, μr, ru, hea, hpw, hsto, hat, hini, hown, hsku, hsig⟩ := locView hi0 hpk htv ho hwcu
  obtain ⟨us, hus, -, hld, -⟩ := locLoad (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat hini hna hsku hsig
      (peek_cell_lyt hi0.2.1 hpk hea rfl rfl).2
        (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_cell_lyt hi0.2.1 hpk hea rfl rfl).2)
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_cell_lyt hi0.2.1 hpk hea rfl rfl).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValR hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ad false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ad false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key] at ⊢
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw ad false us 0 (stOf mem pairs th) → PromAbove r1.1 → MemInv g (CE η) r1.1 :=
    fun r1 h hp => by
      obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
      exact MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  intro r hr hpr
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hvr, hlay, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  by_cases hq : Priv (CE η) ad.label
  · obtain ⟨vq, Rq, R2, H0, hRe, hvql, hvqlat, hvqR, hput⟩ := heldStoreAtP hm hH hq hsto hown (NVP_priv hq)
      (OwnOKPF_cellP hm.2.1 hsto hown hq.2) hat hini hna hvalR hwU hlen
    have hWold : WLe vq old := (loadUnits_latestPA hvql hvqlat h1 hp1).1
    have hvold := oldValR hE.2.1 hE.2.2 hsig (VRR_up _ _ _ _ _ hWold hvqR)
    have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvold hlay
    refine ⟨CE η, Rr + Rq + Rs, R2 + H0, ⟨ρ, η, c', Rr + Rq, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      MemInv_storeAt hm1' hsto hown hat hini hna hval hwUA hlen s2 hs2,
      hput g.k g.arch pw false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hni, hxz, ?_, anchStep_same (bumpIf_nb hterm)⟩
    have h1 := own_le hle z
    have h2 := congrArg (fun R : Res => R (.own z)) hRe
    simp only [Res.add_apply] at h2 ⊢; omega
  · obtain ⟨f, hf⟩ : ∃ f, (CE η).pfr ad.label = some f := by
      cases h : (CE η).pfr ad.label with
      | none => exact absurd ⟨⟨c, hsto, hown⟩, h⟩ hq
      | some f => exact ⟨f, rfl⟩
    obtain ⟨R1, hvold, hz⟩ := oldFree (T := (cl ρ η.wit 0 0 u)) hE.2.1 hE.2.2 (fun _ _ h => h) (fun _ _ _ h => h)
      (TermPlant.noIallV_AtOffP hat (hni _ c hsto)) (noOwn_AtOff hat (MemInv_noOwnT hm hsto hf)) hvr
    have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvold hlay
    refine ⟨CE η, Rr + R1 + Rs, HP, ⟨ρ, η, c', Rr + R1, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      MemInv_storeAt hm1' hsto hown hat hini hna hval hwUA hlen s2 hs2,
      memHeldOn_store (memHeldOn_eqs hH f1 f3) (fun l h e => hq (by rw [e] at h; exact h)) hm1'.2.2.1 hs2, hni, hxz, ?_, anchStep_same (bumpIf_nb hterm)⟩
    have h1 := own_le hle z
    have h2 := hz z
    simp only [Res.add_apply]; omega

/-! ## Word stores -/

/-- **A store at a component keeps the private holding up to the stored value's resources** (own keys). -/
theorem privStoreAt {g : G} {E : TEnv} {s : St} {HP Rv : Res} {a : Address} {c : Cell} {us : List Acc}
    {ws : List Word} {U : Ty} {k : Promises.Knobs} {arch : Arch} {pw : Word} {rel : Bool}
    (hm : MemInv g E s) (hH : MemHeldP E s HP) (hsto : E.sto a.label = some c) (hat : AtOff c.ty a.offset U)
    (hini : Priv E a.label → IniAt E.rc c a U) (hna : ∀ N e, U ≠ .array (.lit N) e)
    (hU : EnvValR E U ws Rv) (hwU : wc U = some (nWords us)) (hlen : ws.length = nWords us) :
    ∀ s', s' ∈ storeUnits k arch pw a rel us ws 0 s →
      ∃ HP', MemHeldP E s' HP' ∧ ∀ y : Nat, HP' (.own y) ≤ HP (.own y) + Rv (.own y) := by
  intro s' hs'
  by_cases hq : Priv E a.label
  · obtain ⟨c0, h0, hown⟩ := hq.1
    rw [hsto] at h0; cases h0
    obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput⟩ := heldStoreAtP hm hH hq hsto hown (NVP_priv hq)
      (OwnOKPF_cellP hm.2.1 hsto hown hq.2) hat (hini hq) hna hU hwU hlen
    refine ⟨R2 + H0, hput k arch pw rel _ rfl rfl (LoadCoh_of_eq hm.2.1 rfl) (fun _ => Nat.le_refl _)
      hm.2.2.2.2.1 s' hs', fun y => ?_⟩
    have h2 := congrArg (fun R : Res => R (.own y)) hRe
    simp only [Res.add_apply] at h2 ⊢; omega
  · exact ⟨HP, memHeldOn_store hH (fun l h e => hq (by rw [e] at h; exact h)) hm.2.2.1 hs', fun y => Nat.le_add_right _ _⟩

/-- A word value's resources, at `CE η`. -/
theorem wordValR {η : TEnv} {n : Nat} {P : Proto} {w : Word} {R : Res}
    (hv : VRR (fun _ => 0) (CE (CE η).unsee) (.word (.lit n) P) (shp (.word (.lit n) P)) [w] R)
    (hV : Valid (.word (.lit n) P) [w]) : EnvValR (CE η) (.word (.lit n) P) [w] R :=
  ⟨VRR_mono _ (CE (CE η).unsee) (CE η) _ _ _ _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) rfl rfl rfl (fun _ _ h => h)
    (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h.elim) (fun _ _ h => h) hv, hV⟩

/-- **The word-store tail** (replaces `TermStep.storeWordC_fin`): the stored word is own-free, so the
frame `Tf ≤ Rf` and the private holding grows by nothing at own keys. -/
theorem k2_wordFin {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {e : Expr}
    {pw w : Word} {A : Address} {n : Nat} {P : Proto} {Rf Rs HP Tf Rv : Res} {z : AllocLabel}
    (hkey : tstep g mem pairs th = (storeUnits g.k g.arch pw A rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s'))
    (hnb : ∀ E1, BumpIf th E1)
    (hmi : ∀ s', s' ∈ storeUnits g.k g.arch pw A rel [.one] [w] 0 (stOf mem pairs th) → MemInv g (CE η) s')
    (hHP : ∀ s', s' ∈ storeUnits g.k g.arch pw A rel [.one] [w] 0 (stOf mem pairs th) →
      ∃ HP', MemHeldP (CE η) s' HP' ∧ ∀ y : Nat, HP' (.own y) ≤ HP (.own y) + (Rv + wdW P n) (.own y))
    (hv : VRR (fun _ => 0) (CE (CE η).unsee) (.word (.lit n) P) (shp (.word (.lit n) P)) [w] (Rv + wdW P n))
    (hfr : FInvR ρ η th.σs (ResumeR p th.stack Rs) c' ((x, .unit, []) :: th.env) Tf) (hle : Tf + Rv ≤ Rf)
    (hE : EnvOK p η) (he : TypedK p η c' e) (htv' : TvOK c') (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRPc : RetPw th.σs th.stack c'.ret) :
    ∀ r ∈ tstep g mem pairs th, StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hkey]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hz := TermBlkZ.VRR_own_zero z (.word (.lit n) P) [] (CE (CE η).unsee) (fun _ => 0) _ [w] _ (by simp [Ty.noOwnIn]) (fun _ _ _ _ h => h.elim)
    (fun _ _ _ _ h => h.elim) hv
  refine stepC_own hnb ⟨ρ, η, c', Tf, Rs, rfl, hE, he, htv', hfr, rfl, hRPc⟩ (hmi s' hs') (hHP s' hs') ?_ hni hx
  have h1 := own_le hle z
  rw [hz]; omega

-- copied from TermStep.storeWordPtrC_core
theorem k2_storeWordPtr {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v tk : At}
    {μ : Mode} {r r' i j k' : Idx} {P : Proto} {c₂ : Nat} {e : Expr} {xt : Ty} {cl' : Clause}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v (some tk)) e)
    (hpk : cx.peek a = .ok (.ptr μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hu : cx.use tk = .ok (.tok r' (some (P, i)), c₁)) (hr : EqI c₁ r r') (hj : IntIdx c₁ v j)
    (hst : InState c₁ P j c₂ k') (hcl : P.clauses[c₂]? = some cl') (hxt : StoreKind xt r' P j cl')
    (hb : c₁.bind x xt = .ok c') (he : TypedK p η c' e) (htv' : TvOK c')
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRPc : RetPw th.σs th.stack c'.ret) :
    ∀ r ∈ tstep g mem pairs th, StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  obtain ⟨hi1, -⟩ := use_FInv hu hi.1
  have ho : cx.opaqueOK (.word r P) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hcellW : ∀ {lab : AllocLabel} {c : Cell}, Fd c.ty (cl ρ η.wit 0 0 (.word r P)) →
      c.ty = .word (.lit (ev ρ r)) P := fun hcty => by
    have h' := hcty; simp only [cl, clI_zero] at h'; exact Fd_word_eq h'
  have hpwf := wordRef_pwf hpk (Or.inl rfl) hμ hi.1 hE htv hm
  rcases hμ with rfl | rfl
  · obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, -, hown, hsku, -⟩ := ownPtr_view hi.1 hpk htv ho
    have hct := hcellW (lab := lab) hcty
    have hat : AtOff c.ty (⟨lab, 0⟩ : Address).offset (.word (.lit (ev ρ r)) P) := by
      rw [hct]; exact .here (Or.inl (by simp [accs, hg]))
    obtain ⟨rt, w, Tf, Rv, hev, hwv, hfr, hle, hvR⟩ :=
      storeWord_frame hi hE.2.2 (RLink_of hE.2.1 hE.2.2) hpwf hg hu hr hj hst hcl hb hxt
    obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    have hus : accs (Ty.word r'' P) = some [.one] := by simp [accs, hg]
    have hval := (Fd_EnvVal (CE η) hcty).2 (storeWord_val (r := r) hpwf hi1.1 hst hwv)
    have husA : accs c.ty = some [Acc.one] := by rw [hct]; simp [accs, hg]
    have hus' : wc c.ty = some (nWords [Acc.one]) := by rw [hct]; simp [wc, accs, hg]
    have key : tstep g mem pairs th =
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
    exact k2_wordFin key (bumpIf_nb hterm) (fun s' hs' => MemInv_store hm hsto hown husA hval rfl s' hs')
      (privStoreAt hm hH hsto hat (fun _ => IniAt_of_ne fun N e h => by rw [hct] at h; cases h)
        (fun N e h => by cases h) (wordValR (hvR _ _) (by rw [← hct]; exact hval.2)) (by simp [wc, accs, hg]) rfl) (hvR _ _) hfr hle hE he htv' hni hx hRPc
  · obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, -, hsku, -⟩ := pubPtr_view hi.1 hpk htv ho
    have hct := hcellW (lab := lab) hcty
    have hat : AtOff c.ty (⟨lab, 0⟩ : Address).offset (.word (.lit (ev ρ r)) P) := by
      rw [hct]; exact .here (Or.inl (by simp [accs, hg]))
    obtain ⟨rt, w, Tf, Rv, hev, hwv, hfr, hle, hvR⟩ :=
      storeWord_frame hi hE.2.2 (RLink_of hE.2.1 hE.2.2) hpwf hg hu hr hj hst hcl hb hxt
    obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    have hus : accs (Ty.word r'' P) = some [.one] := by simp [accs, hg]
    have husc : accs c.ty = some [.one] := by rw [hct]; simp [accs, hg]
    have hval := (Fd_EnvVal (CE η) hcty).2 (storeWord_val (r := r) hpwf hi1.1 hst hwv)
    have key : tstep g mem pairs th =
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
    refine k2_wordFin key (bumpIf_nb hterm) (fun s' hs' => ?_)
      (privStoreAt hm hH hsto hat (fun _ => IniAt_of_ne fun N e h => by rw [hct] at h; cases h)
        (fun N e h => by cases h) (wordValR (hvR _ _) (by rw [← hct]; exact hval.2)) (by simp [wc, accs, hg]) rfl) (hvR _ _) hfr hle hE he htv' hni hx hRPc
    by_cases hown : c.owner = some η.tid
    · exact MemInv_storeF hm hsto hown husc hval rfl s' hs'
    · have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
      exact MemInv_storePubAt (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
        (IniAt_of_ne fun N e he => hna N e he) hna hval husc rfl s' hs'

-- copied from TermStep.storeWordLocC_core
theorem k2_storeWordLocC {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v tk : At}
    {μ : Mode} {r r' i j k' : Idx} {P : Proto} {c₂ : Nat} {e : Expr} {xt : Ty} {cl' : Clause}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v (some tk)) e)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hu : cx.use tk = .ok (.tok r' (some (P, i)), c₁)) (hr : EqI c₁ r r') (hj : IntIdx c₁ v j)
    (hst : InState c₁ P j c₂ k') (hcl : P.clauses[c₂]? = some cl') (hxt : StoreKind xt r' P j cl')
    (hb : c₁.bind x xt = .ok c') (he : TypedK p η c' e) (htv' : TvOK c')
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRPc : RetPw th.σs th.stack c'.ret) :
    ∀ r ∈ tstep g mem pairs th, StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  have hi0 := hi.1
  obtain ⟨hi1, -⟩ := use_FInv hu hi0
  have ho : cx.opaqueOK (.word r P) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
  have hcell : cellOf (Ty.loc μ (.word r P)) = some (μ, .word r P) := by simp [cellOf]
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VR hi0.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ := cell_target hcell (Fd_noarr (by rw [hus1]; simp)) hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, -⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM μ ∧
      etok (skel ru) = etok (skel (close th.σs (.word r P))) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hlr := pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk hcell ho hea rfl
  have hus : accs ru = some [.one] := by rw [hlr, hus1]
  have hat' : AtOff c.ty ad.offset (.word (.lit (ev ρ r)) P) := by simpa only [cl, clI_zero] using hat
  have hpwf := wordRef_pwf hpk (Or.inr rfl) hμ hi.1 hE htv hm
  obtain ⟨rt, w, Tf, Rv, hev, hwv, hfr, hle, hvR⟩ :=
    storeWord_frame hi hE.2.2 (RLink_of hE.2.1 hE.2.2) hpwf hg hu hr hj hst hcl hb hxt
  have hval := storeWord_val (η := η) (r := r) hpwf hi1.1 hst hwv
  have hna : ∀ N e, cl ρ η.wit 0 0 (.word r P) ≠ .array (.lit N) e := fun N e h => by simp [cl] at h
  have hwUA : accs (cl ρ η.wit 0 0 (.word r P)) = some [Acc.one] := hus1
  have hwU : wc (cl ρ η.wit 0 0 (.word r P)) = some (nWords [Acc.one]) := by simp [wc, hus1]
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  refine k2_wordFin key (bumpIf_nb hterm) (fun s' hs' => ?_) (privStoreAt hm hH hsto hat' (fun hq => by
      rcases hμ with rfl | rfl
      · have h4 : IniAt η.rc c ad (.word (.lit (ev ρ r)) P) := by simpa only [cl, clI_zero, modeIni_own_rc] using hini
        exact h4
      · simp only [ModeOK] at hmode
        obtain ⟨f, hf, -⟩ := hmode
        have h3 : η.pfr ad.label = none := hq.2
        rw [hf] at h3; cases h3) (fun N e h => by cases h)
    (wordValR (hvR _ _) (by simpa only [cl, clI_zero] using hval.2)) (by simp [wc, accs, hg]) rfl)
    (hvR _ _) hfr hle hE he htv' hni hx hRPc
  by_cases hown : c.owner = some η.tid
  · exact MemInv_storeAtI hm hsto hown hat (IniAt_mono (modeIni_le_ini _ _ _) hini) hna hval hwUA rfl s' hs'
  · have hpub : μ = .pub := by
      rcases hμ with rfl | rfl
      · exact absurd hmode hown
      · rfl
    subst hpub
    simp only [ModeOK] at hmode
    obtain ⟨f, hf, -⟩ := hmode
    exact MemInv_storePubAt hm hsto hown hf hat hini hna hval hus1 rfl s' hs'

-- copied from TermStep.tstepMC_storeWord
theorem k2_storeWord {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {μ : Mode} {r : Idx} {P : Proto} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) :
    ∀ r ∈ tstep g mem pairs th, StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  have hT0 := hT
  have hCk0 := hCk
  rw [hterm] at hT0 hCk0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk0
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | storeOwn hp hnw | storePub hp hnw | storeRgn hp hnw | storeCap hp hnw =>
    exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | storeWordGive hp hw hu hr hj _ _ hst hcl _ _ hh _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordPtr hterm hpk hμ hg hu hr hj hst hcl (Or.inl ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | storeWordHand hp hw hu hr hj _ _ hst hcl _ _ hh _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordPtr hterm hpk hμ hg hu hr hj hst hcl (Or.inr (Or.inl ⟨rfl, hh⟩)) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | storeWordKeep hp hw hu hr hj _ _ hst hcl _ _ hh _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordPtr hterm hpk hμ hg hu hr hj hst hcl (Or.inr (Or.inr ⟨rfl, hh⟩)) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))

-- copied from TermStep.tstepMC_storeWordLoc
theorem k2_storeWordLoc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {μ : Mode} {r : Idx} {P : Proto} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) :
    ∀ r ∈ tstep g mem pairs th, StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  have hT0 := hT
  have hCk0 := hCk
  rw [hterm] at hT0 hCk0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk0
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | storeOwn hp hnw | storePub hp hnw | storeRgn hp hnw | storeCap hp hnw =>
    exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | storeWordGive hp hw hu hr hj _ _ hst hcl _ _ hh _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordLocC hterm hpk hμ hg hu hr hj hst hcl (Or.inl ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | storeWordHand hp hw hu hr hj _ _ hst hcl _ _ hh _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordLocC hterm hpk hμ hg hu hr hj hst hcl (Or.inr (Or.inl ⟨rfl, hh⟩)) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | storeWordKeep hp hw hu hr hj _ _ hst hcl _ _ hh _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordLocC hterm hpk hμ hg hu hr hj hst hcl (Or.inr (Or.inr ⟨rfl, hh⟩)) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))

-- copied from TermStep.tstepMC_storeWordGhost
theorem k2_storeWordGhost {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {t : Ty} {μ : Mode} {r : Idx} {P : Proto} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P))
    (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = true)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  obtain ⟨rt, pw, b, μ', ru, hea, hc, hab, hus⟩ := ghostRefK hpk ht hμ hg hi.1 hE htv
  have hnw : wordOf t ≠ none := by rcases ht with rfl | rfl <;> simp [wordOf]
  have hT0 := hT
  have hCk0 := hCk
  rw [hterm] at hT0 hCk0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk0
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  have fin : ∀ {Tf : Res}, FInvR ρ η th.σs (ResumeR p th.stack Rs) c' ((x, .unit, []) :: th.env) Tf →
      Tf ≤ Rf → (∃ rv w, evalAt th.env v = some (rv, [w])) →
      ∀ r ∈ tstep g mem pairs th, StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
    intro Tf hfr hle hevx
    obtain ⟨rv, w, hev⟩ := hevx
    have key : tstep g mem pairs th =
        [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
          withS { th with term := e, env := (x, .unit, []) :: th.env } (stOf mem pairs th))] := by
      simp only [tstep, hterm, evalOp, hea, hev, hc, hab, hus, storeUnits, List.map]
    rw [key]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    refine ⟨CE η, Tf + Rs, HP, ⟨ρ, η, c', Tf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩, hm, hH, hni, hx, ?_,
      anchStep_eqs rfl rfl⟩
    have h1 := (Res.le_def.1 hle) (.own z)
    simp only [Res.add_apply] at h1 ⊢
    omega
  have hL := RLink_of hE.2.1 hE.2.2
  cases hop with
  | storeOwn hp hnw' | storePub hp hnw' | storeRgn hp hnw' | storeCap hp hnw' =>
    exfalso; rw [hpk] at hp; cases hp; exact hnw hnw'
  | storeWordGive hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    obtain ⟨-, -, Rt, Rr, -, -, -, -, hi1, hle⟩ := useR hu hi hE.2.2
    obtain ⟨tv, htvk, hio⟩ := hj
    obtain ⟨rv, w, hev, -, -⟩ := atom_num hi1.1.2.1 htvk hio
    have hfr := bindR hb hi1 hL (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    rw [Res.add_zero] at hfr
    exact fin hfr (Res.le_def.2 fun k => by
      have := (Res.le_def.1 hle) k; simp only [Res.add_apply] at this; omega) ⟨rv, w, hev⟩
  | storeWordHand hp hw hu _ hj _ _ hst _ _ _ _ _ _ hb =>
    obtain ⟨-, -, Rt, Rr, -, -, -, -, hi1, hle⟩ := useR hu hi hE.2.2
    obtain ⟨tv, htvk, hio⟩ := hj
    obtain ⟨rv, w, hev, -, -⟩ := atom_num hi1.1.2.1 htvk hio
    have hfr := bindR hb hi1 hL (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    rw [Res.add_zero] at hfr
    exact fin hfr (Res.le_def.2 fun k => by
      have := (Res.le_def.1 hle) k; simp only [Res.add_apply] at this; omega) ⟨rv, w, hev⟩
  | storeWordKeep hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    obtain ⟨rt0, ws0, Rt, Rr, hev0, hv0, hl0, hvt, hi1, hle⟩ := useR hu hi hE.2.2
    simp only [VRR] at hvt
    obtain ⟨tv, htvk, hio⟩ := hj
    obtain ⟨rv, w, hev, -, -⟩ := atom_num hi1.1.2.1 htvk hio
    have hfr := bindR (R := Rt) (rt := .unit) (ws := []) hb hi1 hL (by simp only [VRR]; exact hvt) (tok_Lay _ _ _ _)
    exact fin hfr (by rw [Res.add_comm]; exact hle) ⟨rv, w, hev⟩

-- copied from TermStep.tstepMC_storeWordAny
theorem k2_storeWordAny {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {t : Ty} {μ : Mode} {r : Idx} {P : Proto} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P))
    (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, StepC p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  cases hg : P.ghost
  · rcases ht with rfl | rfl
    · exact k2_storeWord hterm hP hpk hμ hg hT hCk hi hE htv hm hH hni hx hRP
    · exact k2_storeWordLoc hterm hP hpk hμ hg hT hCk hi hE htv hm hH hni hx hRP
  · exact k2_storeWordGhost hterm hP hpk ht hμ hg hT hCk hi hE htv hm hH hni hx hRP hPS

/-! ## The package -/

/-- The plain `FInv` from `FInvR` (for `ScopeOK`). -/
theorem finvK2 {p : Prog} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rs Rf : Res}
    (htv : TvOK cx) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf) :
    FInv ρ η th.σs (Resume p th.stack) cx th.env :=
  FInvR_FInv (htv.2.2.2.2.2.2.2)
    (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs E rd ws R h) hi

/-- **Package K2** (`load`, `store`, `xchg`, `loadAt`, `loadAtF`): every step keeps the own-key total. -/
theorem ownXStep_k2 [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} [ProgRetIall p]
    (hP : ProgT p) (hPS : PwSkel) : ∀ n, OwnXStepPkg p k arch i x n 2 := fun n =>
  ownXStepPkg_of_local (ownXStepL_of (fun g mem pairs th r ρ η cx Rf Rs HP _ _ hq hsc _ hE hT htv hi hRP hm hH _ hni hxz
      hr hpa _ => by
    have hq : exprPkg th.term = 2 := hq
    have hsd := hsc ρ η cx hE hT.1 htv (finvK2 htv hi)
    have hT0 := hT.1
    generalize ht : th.term = t0 at hT0 hsd hq
    have hsc' : StepScope cx t0 := by
      rcases hsd with h | ⟨-, _, _, ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact h
      all_goals (subst h; simp [exprPkg, opPkg] at hq)
    cases hT0 with
    | let_ hop _ =>
      cases hop with
      | loadWord hpk hw =>
        obtain ⟨μ, hteq | hteq⟩ := wordOf_cases hw <;> subst hteq
        · cases μ with
          | own => exact k2_loadWordOwn ht hP hpk hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          | pub => exact k2_loadWordPub ht hP hpk hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          | rgn r' => exact ((hsc' _ hpk) r' _ rfl).elim
        · cases μ with
          | own => exact k2_loadWordLoc ht hP hpk (.inl rfl) hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          | pub => exact k2_loadWordLoc ht hP hpk (.inr rfl) hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          | rgn r' => exact ((hsc' _ hpk) r' _ rfl).elim
      | storeWordGive hpk hw | storeWordKeep hpk hw | storeWordHand hpk hw =>
        obtain ⟨μ, hteq⟩ := wordOf_cases hw
        cases μ with
        | own => exact k2_storeWordAny ht hP hpk hteq (.inl rfl) hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
        | pub => exact k2_storeWordAny ht hP hpk hteq (.inr rfl) hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
        | rgn r' => rcases hteq with rfl | rfl <;> exact ((hsc' _ hpk) r' _ rfl).elim
      | loadRgn hpk _ hc | loadCap hpk _ hc | loadTorn hpk _ hc => exact absurd hc (hsc' _ hpk _ _)
      | storeRgn hpk _ hc | storeCap hpk _ hc => exact absurd hc (hsc' _ hpk _ _)
      | loadOwn hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact k2_loadOwn ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
        · exact k2_loadLoc ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
      | loadPub hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact k2_loadPub ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
        · exact k2_loadPubLoc ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
      | storeOwn hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact k2_storeOwn ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
        · exact k2_storeLoc ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
      | storePub hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact k2_storePub ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
        · exact k2_storePubLoc ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
      | xchg hpk hx =>
        cases hx with
        | own _ hc =>
          rcases cell_cases hc with rfl | rfl
          · exact k2_xchgOwn ht hP hpk hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          · exact k2_xchgLoc ht hP hpk hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
        | rgn _ hc => exact absurd hc (hsc' _ hpk _ _)
      | loadAt => exact k2_loadAt ht hP hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
      | loadAtF => exact k2_loadAtF ht hP hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
      | _ => simp [exprPkg, opPkg] at hq
    | _ => simp [exprPkg] at hq))

end TermOwnK2

#print axioms TermOwnK2.k2_loadOwn
#print axioms TermOwnK2.k2_loadLoc
#print axioms TermOwnK2.k2_loadAt
#print axioms TermOwnK2.k2_loadAtF
#print axioms TermOwnK2.k2_loadPub
#print axioms TermOwnK2.k2_loadPubLoc
#print axioms TermOwnK2.k2_loadWordOwn
#print axioms TermOwnK2.k2_loadWordPub
#print axioms TermOwnK2.k2_loadWordLoc
#print axioms TermOwnK2.k2_storeOwn
#print axioms TermOwnK2.k2_storeLoc
#print axioms TermOwnK2.k2_storePub
#print axioms TermOwnK2.k2_storePubLoc
#print axioms TermOwnK2.k2_xchgOwn
#print axioms TermOwnK2.k2_xchgLoc
#print axioms TermOwnK2.k2_storeWordAny
#print axioms TermOwnK2.ownXStep_k2
