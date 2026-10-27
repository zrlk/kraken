/-
**`hello1`'s per-allocation premises of `allocW2At_of`** (x86-64; the twin
of the per-allocation part of `Spike/Test/A64Hello1HAWNone.lean`): at the
setup frame's allocation of `rodata` (`let b = newBuf m LanesU8`, the only
allocation of `hello1o`'s blocks), the premises `AllocPtW`
(`Spike/Lib/LowerX64/AllocW2AtOf.lean`) beyond the arena's words.

- `hello1_rodata_compiled2`, `hello1_rodata_nbTail`: every allocation on
  the walk of a compiled block of `hello1o` is `rodata`'s `eB` (decided
  over `tailsL`);
- `hello1_rodata_packLeaf`: the count's layout a leaf (`hleaf`);
- `hello1_rodata_count2`: the count the immediate `2`;
- `hello1_hnr`, `hello1_hacc`: the continuation no `main` return at the
  setup frame, the element's accesses;
- `hello1_allocPt`: `OpenAPt` (`Spike/Test/X64Hello1HAWNone.lean`) at
  `hello1o`, the landings `ElH` and the write tail `fun _ => True`: the
  fields above, `hu` and `hms` (`Spike/Test/X64Hello1AllocMs.lean`),
  `hstub` (`hello1_rodata_hstub`), and `hxa`, `hxaF` by `landStk_hxa` at
  the setup frame's context `CxOkH` with no records (its witnesses as in
  `setupOpenF_ofPreH`, its key the bottom key `BotH`), the setup call's
  return address of the phase anchor's phase (`raOk_setup`), the
  resumption point `BodyPtW` from `PtC2` and `Fresh`, the arena's units
  (`arOf_units_fit`); for `hxaF` at the family `J'`, the call's premises
  rebuilt there (`callOK_msOfAX`).
-/
import Spike.Test.X64Hello1HAWNone
import Spike.Test.X64Hello1AllocHS
import Spike.Test.X64Hello1AllocMs
import Spike.Test.X64Hello1HsOf
import Spike.Test.X64Hello1ClosedAt2B
import Spike.Test.X64Hello1CxOkH
import Spike.Test.X64Hello1H1Of
import Spike.Test.Hello1MainFacts
import Spike.Lib.LowerX64.AllocW2AtOf
import Spike.Lib.LowerX64.LandStk2
import Spike.Lib.LowerX64.LandHu
import Spike.Lib.LowerX64.CalleeRgn2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Spike.Lib.LowerNode (compiled2 TailAt2)
open Spike.Lib.Hello1RodataSrc (rdBody eM eB eW0 eO0 eW1 eO1 eN eSm eSl0 ePack eRet τ8)

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `hello1o`'s first compiled block is `rodata`, of body `rdBody`. -/
theorem hello1_rodata_compiled2 : ((compiled2 P1)[0]?).map (·.body) = some rdBody := rfl

/-- **`hello1o`'s allocations are `rodata`'s `eB`**: at every compiled block
in range, an allocation on the walk (`TailAt2`) binds `b` to a buffer of
`m` `LanesU8` elements and continues at `eW0` (`rodata`'s points listed;
`main`'s, at the second block, allocation-free; no third block). -/
theorem hello1_rodata_nbTail {j : Nat} {d : Decl} (hd : (compiled2 P1)[j]? = some d) {x : String} {cn : At}
    {τ : Ty} {e : Expr} (ht : TailAt2 P1 j (.let_ x (.newBuf cn τ) e)) :
    x = "b" ∧ cn = .var "m" ∧ τ = τ8 ∧ e = eW0 := by
  have hm := tailOf_mem_tailsL (ht d hd)
  match j, hd with
  | 0, hd =>
    have hb : d.body = rdBody := by
      have := hello1_rodata_compiled2; rw [hd] at this; exact Option.some.inj this
    rw [hb] at hm
    simp only [tailsL, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet, List.mem_cons,
      List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h <;> (try simp_all) <;> rfl
  | 1, hd =>
    have hc : (tailsL d.body).all (fun t => match t with
        | .let_ _ (.newBuf _ _) _ => false
        | _ => true) = true := by
      have := Spike.Test.Hello1MainSrc.hello1_main_compiled2; rw [hd] at this
      cases this; decide
    simpa using List.all_eq_true.mp hc _ hm
  | k + 2, hd =>
    have h2 : (compiled2 P1)[k + 2]? = none := by
      rw [List.getElem?_eq_none_iff]
      have hl : (compiled2 P1).length = 2 := rfl
      omega
    rw [h2] at hd; cases hd

/-- **The count's literal words are one word** (`AllocPtW.hleaf` at
`rodata`'s allocation): at the literal walk from `eB` with the layouts
`lits`, the slice's `pack` at `ePack` packs `sl0`, laid out as
`((b, m), n)`, at the slice's type (`LitPt`'s `Compat`), so `m`'s layout,
unchanged since `eB` (no later binding of `m`), is a leaf. -/
theorem hello1_rodata_packLeaf {lits : List (String × Scc.Lower.LitV)}
    (hL : ∀ q ∈ Scc.Lower.litWalk2 P1 lits eB, Spike.Lib.LowerNode.LitPt q) :
    ∃ o, Scc.Lower.litAt lits (.var "m") = .leaf o := by
  have hlen : 8 < (Scc.Lower.litWalk2 P1 lits eB).length := by
    simp [Scc.Lower.litWalk2, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet]
  have hP := (hL _ (List.getElem_mem hlen)).2.1 "sl" (.var "sl0") "m" (.iex Spike.Lib.Hello1Src.sliceTy) eRet rfl
  revert hP
  simp only [Scc.Lower.litWalk2, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, List.getElem_cons_succ,
    List.getElem_cons_zero, Scc.Lower.litAt, Scc.Lower.opLit, List.lookup, Spike.Lib.Hello1Src.sliceTy]
  cases hm : lits.lookup "m" with
  | none => intro _; exact ⟨none, rfl⟩
  | some v =>
    cases v with
    | leaf o => intro _; exact ⟨o, rfl⟩
    | _ => simp (config := { decide := true }) [Spike.Lib.LowerNode.Compat, Scc.Obj.coupledPair]

/-- **The count is the immediate `2`** at `rodata`'s allocation: `m`'s word
an immediate `kv` in the lowering's environment (`atomV`), grouped
(`GrpL`, one word: `group_one`), so placed as `.one (.imm kv)` and `kv` the
theorem's table's entry at `eB` (`ImmIn`), `imms2Of hello1o`'s there
(`imms2Me_tailAt2`), `2`. -/
theorem hello1_rodata_count2 {Λ : Scc.Sem.Layout} {j : Nat} {d : Decl} (hd : (compiled2 P1)[j]? = some d)
    (ht : TailAt2 P1 j eB) {env : Scc.Lower.Env} (hg : Spike.Lib.LowerNode.GrpL env)
    (hi : Spike.Lib.LowerNode.ImmIn (Spike.Lib.LowerNode.imms2Me Λ P1) (Spike.Lib.LowerNode.ofEnv2 env) eB)
    {tk : Ty} {kv : UInt64} (hat : Scc.Lower.Inv.atomV env (.var "m") = some (tk, [.imm kv])) :
    kv.toNat = 2 := by
  obtain ⟨b, hb, hv⟩ := Spike.Lib.LowerShape.atomV_var hat
  obtain ⟨rfl, hw⟩ := Prod.mk.inj hv.symm
  obtain ⟨pls, hp⟩ := Option.isSome_iff_exists.mp (hg _ _ hb)
  rw [hw] at hp
  have hpl := Spike.Lib.LowerNode.group_one hp
  have hl : Spike.Lib.Form.lookupS (Spike.Lib.LowerNode.ofEnv2 env) "m" = some (b.2.1, [.one (.imm kv)]) := by
    rw [Spike.Lib.LowerNode.lookupS_ofEnv2, hb]; simp [hw, hp, hpl]
  have h1 := hi "m" 0 kv (by rw [hl]; rfl)
  rw [Spike.Lib.LowerNode.imms2Me_tailAt2 Spike.Lib.LowerNode.hello1o_accepted2 hd ht] at h1
  have h2 : Scc.Lower.imms2Of P1 eB "m" 0 = some 2 := by decide
  rw [h2] at h1
  exact (Option.some.inj h1).symm

/-- **No `main` return past the setup frame's allocation** (`AllocPtW.hnr`):
the frames `[fr]` are not empty. -/
theorem hello1_hnr {fr : TermRun.Frame} {e : Expr} : [fr] = [] → ∀ a, e ≠ .ret a := nofun

/-- **`LanesU8`'s accesses** (`AllocPtW.hacc` at `rodata`'s element type). -/
theorem hello1_hacc : ∃ us, TermRun.accs (TermRun.close [] τ8) = some us := ⟨_, rfl⟩

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

/-- The compiler's output. -/
local notation "OX" =>
  Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes SccCertificate.labelOffs

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "LYx" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Le P1)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOPx" => Spike.Lib.X64.Flow.Ret0.stacksA (LYx).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TPx" => Spike.Lib.X64.Flow.Ret0.tpOf (Spike.Lib.X64.Flow.Ret0.pinA (LYx).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RCx" => ((Spike.Lib.X64.swR v (-L) 0).callee (-8 - 0) (8 - L) 8).callee
  (-8 - (Spike.Lib.X64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 P1)).Z.toInt - 8 - 0) (-D1) 8

/-- **`OpenAPt` at `hello1o`** (the landings `ElH`, the write tail
`fun _ => True`): `AllocPtW` at `rodata`'s allocation at every choice of
the bounds, family containing the starts and setup frame (see the module
docstring). -/
theorem hello1_allocPt : ∀ E : Scc.Sem.Entry, E.Ok (lay2 Le P1) →
    ∀ h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true,
      OpenAPt h Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h) (fun _ => True) := by
  intro E _ h L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn v hv F' g fr hP hSB c0 pc kk x cn τ e env n lits cs
    bufs tk kv en em hh hc0 hT hfr hat hco hhd hpt
  -- the setup frame's context with its (no) records: `CxOkH`'s witnesses as in `setupOpenF_ofPreH`
  have hcx : CxOkS (p := P1) (lbl := fun _ => none) (lsize := fun _ => 0)
      (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h Le)
      (CxOkH h Spike.Lib.LowerNode.hello1o_accepted2) (BotH h) j RCx F' [fr] g.fp g.ra TPx
      (fun c => Spike.Lib.FrameRunM P1 (g.c0, [fr]) (c, [fr]))
      (AbU2 P1 (MSAt h (Spike.Lib.LowerNode.imms2Me Le P1) P1 Spike.Lib.LowerNode.IsNum J (ab2 P1 (LYx).lab)
          (fun _ => 0)) (fun _ => none) (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h Le j d hd)
        (rbR RCx) F' [fr] g.fp g.ra (fun c => Spike.Lib.FrameRunM P1 (g.c0, [fr]) (c, [fr]))) := by
    obtain ⟨-, hfS, -, hnS, -, -, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, -, hL1, -⟩ := id hB
    have hs' : (Scc.Lower.setupOf P1).isSome = true := by rw [hello1_hty.choose_spec]; rfl
    have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h Spike.Lib.LowerNode.hello1o_accepted2 hs')
      (rtCodeOkS_setupWords2 h Spike.Lib.LowerNode.hello1o_accepted2 hs')).1
    have hZ := setupMC_Z _ hsw
    subst hv
    have hok : (Spike.Lib.X64.swR TOPx (-L) 0).OK := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
    have htop8 : (TOPx).toNat % 8 = 0 := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (LYx); omega
    have hR1 : ((Spike.Lib.X64.swR TOPx (-L) 0).callee (-8 - 0) (8 - L) 8).OK :=
      Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
        (by show _ ≤ (0 : Int); omega)
    have hb1 : (((Spike.Lib.X64.swR TOPx (-L) 0).callee (-8 - 0) (8 - L) 8).base.toNat : Int) =
        (TOPx).toNat - 8 :=
      Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
    have hbc := Region.callee_base (hi' := 8)
      (kc := -8 - (Spike.Lib.X64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 P1)).Z.toInt - 8 - 0)
      (lo' := -D1) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
    refine CxOkS.bot ⟨d, hd, L, D1, fS, nS, _, g, fr, J, hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
      ⟨hP.1, ?_, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1, hP.2.2.2.2.2.1, hP.2.2.2.2.2.2⟩,
      fun m hm => (hP.2.2.1 m hm).1.1.1, hSB, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨⟨J, L, D1, fS, _, D2, lS, lM, nS, fM, nM, hB, hSB⟩, d, hd, hn⟩
    omega
  have hc := Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h
  -- the setup call's return address has the phase anchor's phase
  have hra : Spike.Lib.X64.PhRec.ph (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of P1))
        (Int64.ofBitVec g.ra).toBitVec.toNat =
      Spike.Lib.X64.PhRec.ph (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of P1))
        ((Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of P1)).lab raL).toBitVec.toNat := by
    rw [hP.2.2.2.1]
    exact raOk_setup _ _
  -- the allocation a resumption point of the block's code
  have hpt' : BodyPtW (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h Le j d hd) g.ra pc
      (.let_ x (.newBuf cn τ) e) env n lits cs bufs := by
    obtain ⟨l, k, r, h1, h2, h3, h4, h5, h6, h7⟩ := hpt
    unfold BodyPtW
    rw [(fnCode2OfPMe_spec Spike.Lib.LowerNode.hello1o_accepted2 h Le j d hd).2.1]
    exact ⟨l, k, r, kk, h1, hfr, h2, h3, h4, h5, h6, h7⟩
  have hnb : NbArgs (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h Le j d hd).lcx env cn τ hh kv
      (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv) :=
    ⟨tk, en, em, hat, hco, hhd, rfl⟩
  have hel := hello1_rodata_elem2 hd hn x cn τ e hT
  have hst := hello1_rodata_hstub h Spike.Lib.LowerNode.hello1o_accepted2 hello1_hty.choose_spec (E := E)
    (El := ElH h) hB J hd hn hv hP (c0 := c0) (kv := kv) (en := en) (em := em) (hh := hh) hel hpt
  have hl := (fnCode2OfPMe_spec Spike.Lib.LowerNode.hello1o_accepted2 h Le j d hd).1
  have hbl := (fnCode2OfPMe_spec Spike.Lib.LowerNode.hello1o_accepted2 h Le j d hd).2.1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hello1_rodata_nbTail hd hT
  rw [hl] at hco hhd
  have hpt' := hpt
  rw [hl] at hpt'
  obtain ⟨-, -, -, -, -, -, hWs, hLs, -, -⟩ := hpt'
  obtain ⟨hi, -, -, hg, -⟩ := Spike.Lib.LowerNode.walk2_head hWs
  have hk := hello1_rodata_count2 hd hT hg hi hat
  refine ⟨hello1_rodata_packLeaf fun q hq => (hLs q hq).1, hello1_rodata_hu _ hk, hello1_hacc,
    hello1_hms h hco hhd, hello1_hnr, ?hxa, ?hxaF, hst⟩
  case hxa =>
    intro lw zs zc k hla hzs hcla hk'
    exact landStk_hxa (Spike.Lib.X64.Rt.arOf_ok h hc) (startsN_of_startsS hJ) Spike.Lib.AllocReach.Reach.base hd
      hcx hra hc0 hpt' hnb hla hzs hcla (by rw [hbl]; exact hk') (arOf_units_fit _)
  case hxaF =>
    intro lw zs zc k hla hzs hcla hk' q hq J' hJ' l b w s c hl hAt htp
    exact landStk_hxa (J := J') (Spike.Lib.X64.Rt.arOf_ok h hc) hJ' Spike.Lib.AllocReach.Reach.base hd
      hcx hra hc0 hpt' hnb hla hzs hcla (by rw [hbl]; exact hk') (arOf_units_fit _) ⟨q, callOK_msOfAX hq⟩ _
      (fun m hm => hm.1) (fun m hm => hm.2.2) l b w s c hl hAt htp

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_nbTail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_rodata_nbTail

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_packLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_rodata_packLeaf

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_count2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_rodata_count2

/-- info: 'Spike.Lib.LowerX64.hello1_allocPt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_allocPt
