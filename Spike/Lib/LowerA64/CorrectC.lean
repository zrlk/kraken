/-
**The AArch64 compiler theorem for an `Accepted1` program with calls**
(`a64_scc_correctE_text_closedAtC`, the twin of
`Spike/Lib/LowerX64/CorrectC.lean`): `Spike/Lib/LowerA64/Correct1.lean`'s
`a64_scc_correctE_text_closedAt1` for any `Accepted1` program `p` in place
of `[d]`, at the immediates `imms1Of p`, without the frame bound `4095`,
given the configuration's `CfgNeedOkA`. The lowering lowers calls plain
(no frames limit), so every code block's code facts are at no frames limit
(`LowerNoneS`, `lowerNoneS_ofPlaceOK`).

- `lowerAll?_ok_of_placeOKC`: the lowering succeeds on an output passing
  `placeOKAt` (`lowerAll?_ok_of_placeOK` for any program);
- `mainFunc_of_accepted1`: the IR has the stack-checked user `main`, at its
  index;
- `UserMainS`: `a64_lower_correctES_of_user`'s `hU` at a depth `D` and
  limit room `ZU`;
- `userMainSW_of`: `UserMainS` at `main`'s depth `needDA n` and frame from
  the code facts with no frames limit (`fnSpecC_all_ofPlaceOK`,
  `mainPre_of`, `abC_lag`, inside `userCallWS_of_exitCL`);
  `userMainSW_ofPlaceOK`: at the code facts of `lowerNoneS_ofPlaceOK`;
- `a64_lower_correctEC`: at an admissible entry state, `D := needDA n` at
  `main`'s context `ctxOf ir fi f` and row `n` (`mainRoom_of_placeOKAt`),
  `ZU` its frame (`hroomU_ofPlaceOK'` within `mainFrameU_of_placeOKAt`'s
  `12240`);
- `a64_scc_correctE_closedAtC`, `a64_scc_correctE_text_closedAtC`: at any
  layout passing `placeOKAt`; the latter on the text.
-/
import Spike.Lib.LowerA64.StartCorrectS
import Spike.Lib.LowerA64.MainRoomU
import Spike.Lib.LowerA64.PreC
import Spike.Lib.LowerA64.UserLag

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Sem
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Code1A64 (ctxOf)
open Scc.Lower.Inv (Res1 func1 params1R)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1)
open Spike.Lib.A64Consumer (TParE)
open Spike.Lib.A64ConsumerS (SFactsS msOfS)
open Spike.Lib.A64.Rt (RuntimeLayout bareMC)
open Spike.Lib.A64.Flow.Ret0 (limA)
open Spike.Lib.A64.PhRec (μ K)

section Correct

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)

/-- The value invariant: the first TCB's limit word holds its loaded value or the limit. -/
local notation "G0" h:max => Spike.Lib.A64.PhRec.GOf (Ly h) (Spike.Lib.A64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs)

set_option maxRecDepth 100000 in
/-- **The lowering succeeds on an output passing `placeOKAt`**
(`lowerAll?_ok_of_placeOK` for any program): where `lowerAll?` fails,
`lowerAll`'s output is empty and fails the check (A11). -/
theorem lowerAll?_ok_of_placeOKC {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) :
    ∃ em, Scc.Lower.A64.lowerAll? cfg p = .ok em := by
  cases he : Scc.Lower.A64.lowerAll? cfg p with
  | ok em => exact ⟨em, rfl⟩
  | error _ =>
    unfold Scc.Lower.A64.lowerAll at h
    rw [he] at h
    have h0 : placeOKAt pcfg Λ (Out.ofEmitted (default : Scc.Lower.A64.Emitted)) = false := by
      simp [placeOKAt, Checks.ok, checks, show a11 (Out.ofEmitted (default : Scc.Lower.A64.Emitted)) ⟨Λ⟩ = false
        from rfl]
    exact absurd h (by rw [h0]; decide)

/-- **The IR has the stack-checked user `main`**: for an `Accepted1`
program lowered to `em`, `func1` of `main`'s closed form, at its index
`fi`. -/
theorem mainFunc_of_accepted1 (hp : Scc.Lower.Accepted1 p = true) {em : Scc.Lower.A64.Emitted}
    (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em) :
    ∃ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx ∧
      f.name = Scc.Lower.Names.user "main" ∧ f.checkStack = true := by
  obtain ⟨rs, rt, hrs, -, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted1_a64 cfg hp hlow
  have hm : p.any (·.name == "main") = true := by
    simp only [Scc.Lower.Accepted1, Bool.and_eq_true] at hp
    exact hp.1.1.2
  obtain ⟨dm, hf⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr (List.any_eq_true.mp hm) : (p.find? (·.name == "main")).isSome)
  have hn : dm.name = "main" := by simpa using List.find?_some hf
  obtain ⟨i, hi, rfl⟩ := Spike.Lib.LowerNode.find_index hf
  have hmem := Spike.Lib.LowerNode.mem_progOf_funcs1 cfg.layout rt hrs i hi
  rw [← hir] at hmem
  exact ⟨_, _, hmem, by show Scc.Lower.Names.user p[i].name = _; rw [hn], rfl⟩

/-- **The user `main`'s call interface at depth** (`a64_lower_correctES_of_user`'s
`hU`) at a depth `D` and limit room `ZU`: for every switch value,
`UserCallWS` inside `SFactsS` at the arena's `cells` and the overflow
stub's write tail. -/
def UserMainS {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true) (cells : Nat) (D : Int) (ZU : Int64) : Prop :=
  ∀ v, Spike.Lib.A64.Rt.UserCallWS (fun s c fs => SFactsS (Ly h).Λ (μ (Ly h)) p
      (fun s _ => Spike.Lib.A64.PhRec.own (Ly h) s) (Spike.Lib.A64.Rt.rS0 (Ly h)) (Spike.Lib.A64.PhRec.Tk (Ly h))
      (Ly h).Λ.static cells 0 s c fs (OvfDt (Ly h).exe (Ly h).endPc (Ly h).lab))
    (K (Ly h) (Spike.Lib.A64.Rt.rS0 (Ly h))) p (Ly h).Λ.static
    (msOfS (Ly h).Λ (μ (Ly h)) (fun _ => True) (G0 h) (fun s _ => Spike.Lib.A64.PhRec.own (Ly h) s)
      (Ly h).Λ.static (fun _ => 0))
    (Ly h).exe (Ly h).endPc (swR v (-(D + 48)) 0)
    (Spike.Lib.A64.Rt.swFSL (D + 48) (Spike.Lib.A64.Rt.rS0 (Ly h)) (Ret0.stacksA (Ly h).lab + 0#64 + 16384#64)
      (limA (UInt64.ofBitVec (Ret0.pinA (Ly h).lab + 0#64 + 8#64))) v)
    bareMC.fn bareMC.Z D ZU (UPostS p (Ly h).Λ.static Spike.Lib.A64Consumer.c0)
    ((Ly h).lab bareMC.e0 + 4).toBitVec Spike.Lib.A64Consumer.c0
    (UInt64.ofBitVec (Ret0.pinA (Ly h).lab + 0#64 + 8#64))

/-- The placement's memory side at the frames. -/
local notation "MSS" h:max => msOfS (Ly h).Λ (μ (Ly h)) (fun _ => True) (G0 h)
  (fun s _ => Spike.Lib.A64.PhRec.own (Ly h) s) (Ly h).Λ.static (fun _ => 0)

/-- The aborts of the code blocks at their contexts. -/
local notation "AbS" h:max hcode:max => AbC p (O).place.need (Ly h).Λ (Ly h).Λ.static (MSS h)
  (Spike.Lib.A64.Rt.rS0 (Ly h)) hcode

/-- The return addresses in the phase of the one after `scc_rt_main`'s `bl`. -/
local notation "RaOkS" h => fun ra : BitVec 64 => Spike.Lib.A64.PhRec.ph (Ly h) (Int64.ofBitVec ra).toBitVec.toNat =
  Spike.Lib.A64.PhRec.ph (Ly h) (Int64.ofBitVec ((Ly h).lab bareMC.e0 + 4).toBitVec).toBitVec.toNat

/-- The code predicate at a return address. -/
local notation "CdS" h => fun ra : BitVec 64 => CdC (O).prog (Spike.Lib.A64.PhRec.okPc (Ly h))
  (Spike.Lib.A64.PhRec.ph (Ly h)) (Ly h).lab (Int64.ofBitVec ra)

/-- The first stack's top. -/
local notation "TOP" h:max => Ret0.stacksA (Ly h).lab + 0#64 + 16384#64

/-- The first thread's pointer. -/
local notation "TP0" h:max => UInt64.ofBitVec (Ret0.pinA (Ly h).lab + 0#64 + 8#64)

/-- **The user `main`'s interface at depth from the code facts with no
frames limit** (`UserMainS`): for the code facts `hcode` of the closed forms
`rs` with no frames limit and their fields (`CodeFactsS`), at `main`'s row
`n`, `UserMainS` at `main`'s depth `needDA n` and its frame (`ctxOf` at its
index past the runtime's `rt`). Off the first stack's top the switch's
frame condition is empty; at it, `userCallWS_of_exitCL`: the segment from
`main`'s entry `uN0` to its exit is `CalleePre.seg` at `main`'s context
(`mainCtxB`, `mainPre_of`) with every code block's `FnSpecC`
(`fnSpecC_all_ofPlaceOK`), its aborts held back never end (`abC_lag`) and
its return is the interface's (`uPostS_ret`). -/
theorem userMainSW_of (hp : Scc.Lower.Accepted1 p = true) {em : Scc.Lower.A64.Emitted}
    (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hcfg : CfgNeedOkA pcfg = true)
    {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 (LowC p cfg.layout.obj none) p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {cells : Nat} {T : Nat → Expr → Prop} (hT : ∀ j d, p[j]? = some d → ∀ e, T j e → InWalkD none d e)
    (hcode : ∀ j d, p[j]? = some d →
      FnCode (Ly h).exe (Ly h).prog (Ly h).endPc (RaOkS h) (CdS h) (Scc.Lower.imms1Of p) (T j) d)
    (hok : ∀ j d (hd : p[j]? = some d), CodeFactsS h rs rt (hcode j d hd) j)
    {jm : Nat} {dm : Decl} (hdm : p[jm]? = some dm) (hfd : p.find? (·.name == "main") = some dm) {r : Res1}
    (hr : rs[jm]? = some r) {l : String} {f n : Nat}
    (hrow : Scc.Cert.NeedA64.row? (O).place.need (Scc.Lower.Names.user "main") = some (l, f, n)) :
    UserMainS h cells (needDA n)
      (Int64.ofInt (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + jm)
        (func1 (Scc.Lower.Names.user dm.name) (params1R dm) r)).frame) := by
  intro v
  have hnm : dm.name = "main" := by simpa using List.find?_some hfd
  obtain ⟨r', hr', -, -, -, -, -, -, hcxe, -, -, -⟩ := hok jm dm hdm
  obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hr)
  -- `main`'s IR function and its row
  obtain ⟨hjm, hpj⟩ := List.getElem?_eq_some_iff.mp hdm
  obtain ⟨hjr, hrj⟩ := List.getElem?_eq_some_iff.mp hr
  have hf := Spike.Lib.LowerNode.mem_progOf_funcs1 cfg.layout rt hrs jm hjm
  rw [← hir] at hf
  simp only [hpj, hrj] at hf
  have hname : (func1 (Scc.Lower.Names.user dm.name) (params1R dm) r').name = Scc.Lower.Names.user "main" := by
    show Scc.Lower.Names.user dm.name = _; rw [hnm]
  obtain ⟨l1, n1, hr1, -, hn1, -⟩ := mainNeedOkA_of_placeOKAt hp hlow h hcfg hf hname rfl
  rw [hname, hrow] at hr1
  simp only [Option.some.injEq, Prod.mk.injEq] at hr1
  obtain ⟨-, -, hn1'⟩ := hr1
  rw [← hn1'] at hn1
  obtain ⟨cx, l2, n2, D, hcx, hr2, hD2, hfD, -, hD0, hD8, hD⟩ := mainRoom_of_placeOKAt hp hlow h hcfg hf hname rfl
  rw [hname, hrow] at hr2
  simp only [Option.some.injEq, Prod.mk.injEq] at hr2
  obtain ⟨-, hf2, hn2⟩ := hr2
  rw [← hn2] at hD2
  subst hD2
  by_cases hv : v = TOP h
  case neg =>
    intro F'' _ _ _ hFF _ _ _ _
    exact SegWS.empty fun s c fs ⟨⟨_, _, _, _, _, _, hD', _⟩, _⟩ => hv (hFF _ hD').1.1.1
  subst hv
  refine userCallWS_of_exitCL hp rfl Spike.Lib.A64ConsumerS.msAgree_msOfS (ownIncl_of_indep fun _ => rfl) ?_
  intro F'' hR0 _ hF'' hFF g hra hc htp _
  refine ⟨AbS h hcode, g.fp, g.ra, Spike.Lib.A64Consumer.c0, ?_,
    abC_lag hp h hrs hir hT hcode fun j d hd => (hok j d hd).ovfFacts, fun c1 s c hr0 _ hA => uPostS_ret hr0 hA⟩
  by_cases hL : ∃ Z, Ret0.LimOk ((MSS h) [])
      (Spike.Lib.A64.Rt.swFSL (needDA n + 48) (Spike.Lib.A64.Rt.rS0 (Ly h)) (TOP h) (limA (TP0 h)) (TOP h))
      (Ly h).exe (Ly h).endPc (limA (TP0 h)) Z
  case neg =>
    exact SegWS.empty fun s c fs ⟨⟨_, _, _, _, σ, _, _, _, hlim⟩, _⟩ => hL ⟨_, by rw [htp] at hlim; exact hlim⟩
  obtain ⟨Z, hL⟩ := hL
  have hcx' := mainCtxB h hdm hnm hrow hn1 (fun m hm => hm) hR0 hF'' hFF hL
  have hpre := mainPre_of (cells := cells) hp h hcode hok hdm hfd hcx' (fun m hm => (hFF m hm).1)
    (by show -needDA n ≤ _; rw [hcxe, ← hcx]; omega) (by rw [hcxe]) hra hc htp
  have H := hpre.seg (fnSpecC_all_ofPlaceOK hp h hrs hir hT hcode hok jm dm hdm)
    fun σ c hJ => hJ.1.1.2.2.2.2.trans htp
  have hfn : (hcode jm dm hdm).fn = bareMC.fn := by rw [(hcode jm dm hdm).hfn, hnm]; rfl
  rw [hfn] at H
  exact H.mono_pre fun s c fs ⟨hA, hfs⟩ => ⟨at_sp0 hA, hfs⟩

/-- **The user `main`'s interface at depth from the placement check and
the code facts with no frames limit** (`userMainSW_of` at the code facts of
`lowerNoneS_ofPlaceOK`): `main`'s depth `D` and limit room its frame (within
`12240`, `mainFrameU_of_placeOKAt`) with their bounds
(`mainRoom_of_placeOKAt`), and `UserMainS` there. -/
theorem userMainSW_ofPlaceOK (hp : Scc.Lower.Accepted1 p = true) {em : Scc.Lower.A64.Emitted}
    (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em) {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hcfg : CfgNeedOkA pcfg = true) {cells : Nat} :
    ∃ (D : Int) (fsz : Nat), 0 ≤ D ∧ D % 8 = 0 ∧ D + 48 ≤ 16384 ∧ fsz ≤ 12240 ∧
      UserMainS h cells D (Int64.ofInt fsz) := by
  obtain ⟨rs, rt, hrs, hir, T, hT, hcode, hok⟩ := lowerNoneS_ofPlaceOK hp hlow h
  -- `main`'s code block
  have hm : p.any (·.name == "main") = true := by
    simp only [Scc.Lower.Accepted1, Bool.and_eq_true] at hp
    exact hp.1.1.2
  obtain ⟨dm, hfd⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr (List.any_eq_true.mp hm) : (p.find? (·.name == "main")).isSome)
  have hnm : dm.name = "main" := by simpa using List.find?_some hfd
  obtain ⟨jm, hjm, hpj⟩ := Spike.Lib.LowerNode.find_index hfd
  have hdm : p[jm]? = some dm := by rw [List.getElem?_eq_getElem hjm, hpj]
  have hjr : jm < rs.length := hrs.1 ▸ hjm
  have hr : rs[jm]? = some rs[jm] := List.getElem?_eq_getElem hjr
  -- its IR function and row
  have hf := Spike.Lib.LowerNode.mem_progOf_funcs1 cfg.layout rt hrs jm hjm
  rw [← hir] at hf
  simp only [hpj] at hf
  have hname : (func1 (Scc.Lower.Names.user dm.name) (params1R dm) rs[jm]).name = Scc.Lower.Names.user "main" := by
    show Scc.Lower.Names.user dm.name = _; rw [hnm]
  obtain ⟨cx, l, n, D, -, hrow, rfl, -, -, hD0, hD8, hD⟩ := mainRoom_of_placeOKAt hp hlow h hcfg hf hname rfl
  rw [hname] at hrow
  exact ⟨_, _, hD0, hD8, hD, mainFrameU_of_placeOKAt hp hlow h hcfg hf hname rfl,
    userMainSW_of hp hlow h hcfg hrs hir hT hcode hok hdm hfd hr hrow⟩

/-- **The AArch64 compiler theorem for an `Accepted1` program at an
admissible entry state `E`** (`hE`), no static label (`hs`), at a
configuration with `CfgNeedOkA` (`hcfg`), given the code facts with no
frames limit (`lowerNoneS_ofPlaceOK`): `Correct` over the target on parsed
texts at `E`. -/
theorem a64_lower_correctEC (hp : Scc.Lower.Accepted1 p = true) {em : Scc.Lower.A64.Emitted}
    (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em) {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (O) = true) (hs : ∀ l, Λ.static l = none) (hcfg : CfgNeedOkA pcfg = true)
    {B : Scc.Sem.Budget} {arch : WeakMem.Arch} {E : Entry} (hE : E.Ok (Ly h).Λ) :
    Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p) (Ly h).Λ B
      ((O).prog, (O).secs) := by
  obtain ⟨D, fsz, hD0, hD8, hD, hfu, H⟩ := userMainSW_ofPlaceOK (cells := B.cells) hp hlow h hcfg
  exact a64_lower_correctES_of_user hp hlow h hs hE hD0 hD8 hD
    (hroomU_ofPlaceOK' h _ (Int.natCast_nonneg _) (by omega)) H

/-- **The AArch64 compiler theorem for an `Accepted1` program at any
layout**: for a program `p` that `scc` accepts (`hp`), whose output passes
the placement check at a layout `Λ` (`h`) at a configuration with
`CfgNeedOkA` (`hcfg`), the output is `Correct` over the kernel-model target
at every entry state `E` that `Entry.Ok` admits, at `Λ` with no static
label and the lowering's immediates. -/
theorem a64_scc_correctE_closedAtC (Λ : Scc.Sem.Layout) (hp : Scc.Lower.Accepted1 p = true)
    (h : placeOKAt pcfg Λ (O) = true) (hcfg : CfgNeedOkA pcfg = true) {B : Scc.Sem.Budget}
    {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of p } →
      Scc.Sem.Correct (TParE E) (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p)
        { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of p } B ((O).prog, (O).secs) :=
  have h' : placeOKAt pcfg { Λ with static := fun _ => none } (O) = true :=
    (Scc.Cert.PlaceOK.A64.placeOKAt_static pcfg Λ (O) (fun _ => none) Λ.imms).trans h
  fun _ hE =>
    have ⟨_, hlow⟩ := lowerAll?_ok_of_placeOKC h
    a64_lower_correctEC hp hlow h' (fun _ => rfl) hcfg hE

/-- **The AArch64 compiler theorem on the text for an `Accepted1` program,
at any layout** (`Scc.Sem.A64.CorrectE`): for a program `p` that `scc`
accepts (`hp`), whose output passes the placement check at a layout `Λ`
(`h`) at a configuration with `CfgNeedOkA` (`hcfg`, decided on the
configuration) and whose assembler text `asm` the loader parses to it
(`hpa`), the text is `Correct` over the kernel-model target at every
admissible entry state, at `Λ` with no static label and the lowering's
immediates.

If the program exits, it exits as the source does; the theorem does not
promise that it exits. -/
theorem a64_scc_correctE_text_closedAtC (Λ : Scc.Sem.Layout) (hp : Scc.Lower.Accepted1 p = true)
    (h : placeOKAt pcfg Λ (O) = true) (hcfg : CfgNeedOkA pcfg = true) {asm : String}
    (hpa : Scc.Cert.Link.A64.parsesTo asm (O).prog (O).secs = true) {B : Scc.Sem.Budget} {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) p)
      { Λ with static := fun _ => none, imms := Scc.Lower.imms1Of p } B asm :=
  fun E hE =>
    let ⟨h1, h2⟩ := Scc.Cert.Link.A64.parsed_of_parsesTo hpa
    Scc.Sem.A64.correct_of_parsed _ E h1 h2 (a64_scc_correctE_closedAtC Λ hp h hcfg E hE)

end Correct

end Spike.Lib.LowerA64
