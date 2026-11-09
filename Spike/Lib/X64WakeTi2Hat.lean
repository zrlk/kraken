/-
**`HMidPA.ti`'s discharger** (x86-64, the twin of
`Spike/Lib/A64WakeTi2Hat.lean`): wake's second `scc_rt_thread_init` call,
from `wc_main` on the second TCB `t2` returning to `.x21`, is a segment
inside `W1X ∧ NoSetFsAt` under `h1`'s outside move `TakeCK aW r1W ClW`, at
`tpXa ms1 t`, its post the stack `r1W` in private memory.

`Rt.threadInit_segWAtAC` at `r1Of` (`q.k0 = 16384`), its node obligations
`StartTi.ti2_WSP` (inside `StartWf.WS` at `X0T`, the start's level
instantiated at `W1W`'s arena, source, clone and placement), lifted to
`WSX` (`OwnTi2.ti2L`, `TiWAtP.imp`) and to `NoSetFsAt` (`Ti2.tiWAtP_nm`);
`WSX` gives `W1W` (the marks by `AbOffW.marks_target`) and `X1W`
(`x1W_of_x0T`); the take `TakeK` is `TakeCK`'s off the clone's pc
(`SegW.mono_K`).

The callee's frame on the pool and `r1W` off it come from `BoxPure`'s base
(`hbase`: `bandP_box64`, `hout_box64`, `hRS_box64`), main's stack owned at
the site (`owned_r0_64`) from the box's frame off `R` (`hF0`, `StackOff`),
the call's frame (in `R` off the callee's region), the take's frame (`R'`'s
cells off the take's region, `TiWAtP`'s site condition `CallerCells`, via
`ti2_WSP`'s `hXs`) and the take's cells, `R`'s bounds 8-aligned (`hR8`).
Left as named premises: the second TCB's words (`hmF`, `hunF`, `hnoF`,
`hoffT`), the counters off the arena (`hoffL`, `hoffX`), the sources' facts
(`hSctl`, `hpl`), the field and take facts (`hfld`, `htk`), `hF0`. The
child's stack unowned before its take comes from the pre's `Pz r1W`
(`x0T_sitePz`), kept by the callee's frames (`pz_fstable_ti2_64`).

- `hti_W`: `HMidPA.ti` (`WakeH1GOf.TiG`), generic in `E`, `cT`, `Dt`, `Ctx`,
  `ls0`.

**Unlike AArch64**: the take site's frame condition is `Pz r1W ∧
CallerCells R' (-48) (-200) 8` (`Rt.TiWAtP`, `threadInit_segWAtAC`), not
`TiW`'s `.call` `CallerCells`; the start's level is lifted from `ownG` to
`ownGXW` (`WSX`, `ti2L`); the word separation, the rodata, the second
stack's range and the take site are discharged from the layout given A13's
data part (`hA13`: `wsep_W`, `hsub1_W`, `tcbM_ne_ntA_W`, `tcb2_notG_W`;
`hro_W`, `aW_site`), not premises; the source fact is `QB`'s (no `SB`); the
assembly is a parameter `asm`; the regions are x86-64's (`R.callee (-72)
(-248) 8`, `R` ending `64` below the second stack, main's slots at `-16`,
`-8`); `StOk` has no exit pc. No absolute address appears in this file.
-/
import Spike.Lib.X64WakeHatA
import Spike.Lib.X64WakeTi2P
import Spike.Lib.Rt.X64SegsAC
import Spike.Lib.X64WakeTiNoMsrP
import Spike.Lib.X64WakeOwnTi2X
import Spike.Lib.X64WakeOwnStartTiP
import Spike.Lib.X64WakeTi2Box64
import Spike.Lib.X64WakeTi2HatG
import Spike.Lib.X64WakeTi2Slot
import Spike.Lib.X64WakeSrcCtl
import Spike.Lib.X64WakeAWSite
import Spike.Lib.X64WakeOwnSW
import Spike.Lib.X64WakeOwnT2W
import Spike.Lib.X64SiteOfPlaceW
import Spike.Lib.X64WakeAbOffW

namespace Spike.Lib.X64.WakeTi2Hat

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.WakeWc (t2 tiQ stOk_tpXa)
open Spike.Lib.X64.WakePh.WcSp4 (wcNI)
open Spike.Lib.X64.WakePh.Tcb2Call (oC)
open Spike.Lib.X64.Flow.Ret0 (tiN tiX StOk CallerCells StackM TakeK)
open Spike.Lib.X64.KeepTP (NoSetFsAt tpXa)
open Spike.Lib.X64WakeLoadT (L0T ls0T tcb0)
open Spike.Lib.X64.WakeBoxW (W1X)
open Spike.Lib.X64.WakeHMid (QB)
open Spike.Lib.X64ConsumerA (TakeCK)
open Spike.Lib.X64.WakePh.Ti2 (BandP X0T)
open SccCode (wakeCells)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Spike.Lib.X64Consumer.Lsize)
  (l : WeakMem.AllocLabel) (b n : Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => WakeH1Inv.ms1W asm hp i E cT ls0 l b n []

set_option hygiene false in
/-- The end of text. -/
local notation "eR" => WakeH1Inv.endR hp i

set_option hygiene false in
/-- The callee's outside move: the take of the second stack or a `clone` refusal. -/
local notation "KA" => TakeCK (X64WakeOSide.aW hp i E) (X64WakeOSide.r1W hp i) (WakeOD.ClW hp i)

set_option maxHeartbeats 3200000 in
/-- **`HMidPA.ti` at `R`, `F`, `t`**: from the layout's program wake's
(`hpg`, `hlo`, `hpa`), A13's data part (`hA13`) and the named premises of
the file's header, at the pre `Pz r1W`; `BoxPure`'s base `hbase`. -/
theorem hti_W {R : Region} {F : MachineData → Prop} {t : UInt64} (hpg : o.prog = wakeCells)
    (hlo : (Ly).Λ.code.lo = Spike.Lib.X64.WakePh.lo) (hpa : cellsOf asm = some o.prog)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hSctl : ∀ l' A c, QB l b l' A c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf X64WakeT1.wakeSrc c [])
    (hpl : ∀ c0, (∃ l' A', QB l b l' A' c0) → ∀ s : State,
      placeVal (machine (kernel 1)) s (.slot (R.addr (-16)).toNat) = some b →
      placeVal (machine (kernel 1)) s (.slot (R.addr (-8)).toNat) = some (tcb0 (Ly).Λ) →
      Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b) s c0 [])
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m)
    (hmF : ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (t2 (Ly).lab),
      Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) true ⟨a, 8⟩ = true)
    (hunF : ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (t2 (Ly).lab), ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hnoF : ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (t2 (Ly).lab), ∀ j w,
      (⟨a, 8⟩, w) ∉ Spike.Lib.X64.WakePh.own2b (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) j)
    (hoffT : ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (t2 (Ly).lab),
      ¬ ((WakeOD.arW hp i).heap ≤ a.toNat ∧ a.toNat < (WakeOD.arW hp i).heap + 16 * (WakeOD.arW hp i).cells) ∧
      (⟨a, 8⟩ : Loc) ≠ (WakeOD.arW hp i).ctrLoc)
    (hoffL : ¬ ((WakeOD.arW hp i).heap ≤ (Ly).lockA.toNat ∧
        (Ly).lockA.toNat < (WakeOD.arW hp i).heap + 16 * (WakeOD.arW hp i).cells) ∧
      (⟨(Ly).lockA, 8⟩ : Loc) ≠ (WakeOD.arW hp i).ctrLoc)
    (hoffX : ¬ ((WakeOD.arW hp i).heap ≤ (Ly).nextA.toNat ∧
        (Ly).nextA.toNat < (WakeOD.arW hp i).heap + 16 * (WakeOD.arW hp i).cells) ∧
      (⟨(Ly).nextA, 8⟩ : Loc) ≠ (WakeOD.arW hp i).ctrLoc)
    (hbase : R.base.toNat + 64 = (Ly).stacksA.toNat + 16384) (hRs : R.lo ≤ -320 ∧ 0 ≤ R.hi)
    (hR8 : R.lo % 8 = 0 ∧ R.hi % 8 = 0)
    (hF0 : ∀ m, F m → Ret0.StackOff (Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab) R m)
    (hfld : ∀ e ∈ Ret0.ThreadInit.fields (t2 (Ly).lab) (Ret0.stacksA (Ly).lab + 16384#64),
      StOk ms1 F (t2 (Ly).lab + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
      R' = R.callee (-72) (-248) 8 → ∀ (g g' : Ret0.AllocTcb.G),
      Spike.Lib.X64.Rt.TakeOkA ms1 F (Ly).exe eR (R'.callee (-48 - 0) (-200) 8) F'
        (Ret0.tiTake (tiQ (t2 (Ly).lab) c0 g) g')) :
    ∀ (c0 : Ctl), (∃ l' A', QB l b l' A' c0) → ∀ (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64)
      (R' : Region) (F' : MachineData → Prop), cA.toNat = b → m.toNat = tcb0 (Ly).Λ →
      R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi → FStable R' F' → KStable KA F' →
      (∀ m, F' m → F m) → R' = R.callee (-72) (-248) 8 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -72) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.AllocTcb.G,
        (∃ σC c, (wcNI (Ly).lab c0 (t2 (Ly).lab) cA m fr).J σC c ∧
          (tiN (Ly).lab (tiQ (t2 (Ly).lab) c0 g) .e).J (enter (-72) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oC mC σC ∧ (wcNI (Ly).lab c0 (t2 (Ly).lab) cA m fr).J σC c ∧
          (tiN (Ly).lab (tiQ (t2 (Ly).lab) c0 g) .e).J (enter (-72) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -72) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c [] ∧ NoSetFsAt s) KA X64WakeT1.wakeSrc
          (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b) (tpXa ms1 t)
          (fun s c => At (Ly).exe eR R' F' (tiN (Ly).lab (tiQ (t2 (Ly).lab) c0 g) .e) s c ∧
            Spike.Lib.X64Consumer.Pz (X64WakeOSide.r1W hp i) s.st.1)
          (fun s c => ∃ x, At (Ly).exe eR R' F' (tiX (Ly).lab (tiQ (t2 (Ly).lab) c0 g) x) s c ∧
            StackM (X64WakeOSide.r1W hp i) s.st.1) := by
  intro c0 hQB cA m fr R' F' hcA hmw hR hRlo hhi hF hKt hFF hR' hCC g hpre hFm
  subst hR'
  have haW := X64WakeOSide.aW_site hp i hpa E
  have hs := Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hp i hA13
  have hro := X64WakeOSide.hro_W hp i
  have hsub := Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hp i hA13
  have hbd : BandP (Ly) R (-320) := Spike.Lib.X64.WakePh.Ti2.bandP_box64 hbase
  have hfit := Spike.Lib.X64.Rt.fitS_of_sub (Ly) hsub
  have hout := Spike.Lib.X64.WakePh.Ti2.hout_box64 (L := Ly) hbase
  have hRS := Spike.Lib.X64.WakePh.Ti2.hRS_box64 (L := Ly) hbase
  have hlab : ∀ l x, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some x →
      (Ly).lab l = Int64.ofNat x :=
    fun l x h => PlaceWX.hlab_ofPlaceWX hp i l x (by rw [hlo, hpg]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    PlaceWX.abortLbl_of_placeWX (PlaceWX.link i hp)
  have hsite := PlaceWX.site_ofPlaceWX hp i
  have hpL : (Ly).prog = wakeCells := hpg
  have hE : (Ly).endPc = eR := by
    show Scc.Cert.Rt.X64.endOf _ (Ly).prog _ = _; rw [hpL]
  have hrc : Spike.Lib.X64.Rt.RtCodeIn0 (Ly).prog := hpL ▸ Spike.Lib.X64.WakePh.wake_rtCodeIn0
  have hti : Ret0.ThreadInit.threadInitIn (Ly).prog = true := hpL ▸ Spike.Lib.X64.WakePh.wake_tiIn
  obtain ⟨l', A', hS⟩ := hQB
  have hc := hSctl _ _ _ hS
  -- the return address `.x21`, from the caller's node
  have hra : g.ra = ((Ly).lab ".Lwc_main.x3").toBitVec := by
    obtain ⟨σC, c, hw, -, -, -, hx, -⟩ := hpre
    exact hx.symm.trans hw.2.2.1
  -- the take's frame and `r1W`'s stability
  have hSM := Ret0.stackM_stable hfit hout
  have hSMt : FStable ((R.callee (-72) (-248) 8).callee (-48 - 0) (-200) 8)
      (StackM (X64WakeOSide.r1W hp i)) := by
    refine Ret0.stackM_stable hfit fun a h8 ha ha7 => ?_
    show (a : Int) + 8 ≤ (((R.callee (-72) (-248) 8).callee (-48 - 0) (-200) 8).base.toNat : Int) + -200 ∨
      (((R.callee (-72) (-248) 8).callee (-48 - 0) (-200) 8).base.toNat : Int) + 8 ≤ a
    have hb' := Region.callee_base (hi' := 8) hR (show (R.callee (-72) (-248) 8).lo ≤ (-48 - 0) + -200 by omega)
      (by decide) (show (-48 - 0 : Int) < (R.callee (-72) (-248) 8).hi by omega)
    rcases hout a h8 ha ha7 with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  have hal8 : R.base.toNat % 8 = 0 := by have := (Ly).stacks_al; omega
  -- main's slots at the callee's states, for the placement
  have hPlK := Spike.Lib.X64.WakePh.Ti2.slotP_keep64 (L := Ly) hbase ⟨by omega, hRs.2⟩ hcA hmw fun m' h =>
    let ⟨mC, σC, _, hA, hJ, _, hk⟩ := hFm m' h; ⟨mC, σC, hA, hJ.2.2.2.1, hJ.2.2.2.2.1, hk⟩
  -- the take site's frame condition
  let PT : MachineData → Prop := fun m => Spike.Lib.X64Consumer.Pz (X64WakeOSide.r1W hp i) m ∧
    CallerCells (R.callee (-72) (-248) 8) (-48 - 0) (-200) 8 m
  -- the nodes inside `WS` at `X0T`
  have hT := Spike.Lib.X64.WakePh.StartTi.ti2_WSP (P := PT)
    (L := Ly) (a := Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)
    (rS := X64WakeOSide.r1W hp i) (ar := WakeOD.arW hp i) (p := X64WakeT1.wakeSrc) (Dt := Dt)
    (Cl := WakeOD.ClW hp i) (Ctx := fun _ _ _ => False) (lbl := Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
    (lsize := Spike.Lib.X64ConsumerA.updN (ls0T ls0) l n) (frM := ⟨"", c0.term, c0.env, [], .int⟩)
    (X0 := X0T (Ly) (X64WakeOSide.aW hp i E))
    hpL hlo hlab hsite (fun _ h => h.2) hc
    (fun s h => (Spike.Lib.X64.WakePh.Ti2.slotP_place h).elim (hpl c0 ⟨l', A', hS⟩ s)) hPlK
    (Spike.Lib.X64.WakePh.Ti2.x0T_ti hlab haW)
    (Spike.Lib.X64.WakePh.Ti2.bandP_callee hbd (by decide) (by decide)) hΛ hs hro hR hRlo hhi
    (fun m h => hFr m (hFF m h)) (tiQ (t2 (Ly).lab) c0 g) rfl hmF (fun a ha m h => hunF a ha m (hFF m h)) hnoF
    hra rfl hsub hSM hSMt hoffT hoffL hoffX
    (fun s hpc hr hm hP h3 => Spike.Lib.X64.WakePh.Ti2.x0T_sitePz
      (fun h => Spike.Lib.X64.WakeSrcCtl.cloneAt_ne_site hp i hpg h.symm)
      (P := fun s => CallerCells (R.callee (-72) (-248) 8) (-48 - 0) (-200) 8 s.st.1 ∧
        ∀ k, ((R.callee (-72) (-248) 8).callee (-48 - 0) (-200) 8).Off k →
          (Mem.loadInt s.st.1.dmem (((R.callee (-72) (-248) 8).callee (-48 - 0) (-200) 8).addr k) 8).isSome)
      (fun s _ _ hm h4 => Spike.Lib.X64.WakePh.Ti2.owned_r0_64 hbase hal8 hR8 (hF0 _ (hFF _ hm)) (hCC _ hm)
        h4.1 h4.2) s hpc hr hm hP.1 ⟨hP.2, h3⟩)
  -- lifted to `WSX`, then to `NoSetFsAt`
  have htcb : (tiQ (t2 (Ly).lab) c0 g).tcb = Spike.Lib.X64.WakePh.tcb2 (Ly) := by
    show Ret0.pinA (Ly).lab + 136#64 = (Ly).pinA + 136#64; rw [(Ly).lab_pin]
  have hL := Spike.Lib.X64.WakePh.OwnTi2.ti2L (L := Ly) (a := Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)
    (ar := WakeOD.arW hp i) (p := X64WakeT1.wakeSrc) (Dt := Dt)
    (Cl := WakeOD.ClW hp i) (Ctx := fun _ _ _ => False) (lbl := Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
    (lsize := Spike.Lib.X64ConsumerA.updN (ls0T ls0) l n) (frM := ⟨"", c0.term, c0.env, [], .int⟩)
    (X0 := X0T (Ly) (X64WakeOSide.aW hp i E)) (M := StackM (X64WakeOSide.r1W hp i))
    hpL hlab hsite hs.tcb (Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hp i hA13)
    (Spike.Lib.X64.WakePh.tcb2_notG_W hp i hA13)
    (Spike.Lib.X64.WakePh.Ti2.bandP_callee hbd (by decide) (by decide)) hR hRlo hhi
    (fun m h => hFr m (hFF m h)) (tiQ (t2 (Ly).lab) c0 g) htcb (fun a ha m h => hunF a ha m (hFF m h)) hra
  have hTX : ∀ j, Spike.Lib.X64.Rt.TiWAtP
      (Spike.Lib.X64.WakePh.WSX (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) (WakeOD.arW hp i) X64WakeT1.wakeSrc
        Dt (WakeOD.ClW hp i) (fun _ _ _ => False) (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
        (Spike.Lib.X64ConsumerA.updN (ls0T ls0) l n) ⟨"", c0.term, c0.env, [], .int⟩
        (X0T (Ly) (X64WakeOSide.aW hp i E)))
      (Spike.Lib.X64.PhRec.K (Ly) (X64WakeOSide.r1W hp i)) (Ly).exe (Ly).endPc (R.callee (-72) (-248) 8) F'
      (StackM (X64WakeOSide.r1W hp i)) (tiQ (t2 (Ly).lab) c0 g) Ret0.ThreadInit.x7L PT j := fun j =>
    Spike.Lib.X64.WakePh.TiWAtP.imp (hT j) (by rw [Spike.Lib.X64.Rt.tiWAt_x7]; exact hL j)
      fun _ _ h1 h2 => by exact h2 h1
  have hTn := Spike.Lib.X64.WakePh.Ti2.tiWAtP_nm (Ly).lays rfl hti hrc.take hTX
  -- the segment, at `TakeK` of the site
  have hfld' : ∀ e ∈ Ret0.ThreadInit.fields (t2 (Ly).lab) (Ret0.stacksA (Ly).lab + 16384#64),
      StOk (tpXa ms1 t) F (t2 (Ly).lab + BitVec.ofNat 64 e.1) e.2 :=
    fun e he => stOk_tpXa (hfld e he)
  have htk' : ∀ g', Spike.Lib.X64.Rt.TakeOkA (tpXa ms1 t) F (Ly).exe (Ly).endPc
      ((R.callee (-72) (-248) 8).callee (-48 - 0) (-200) 8) F' (Ret0.tiTake (tiQ (t2 (Ly).lab) c0 g) g') := by
    intro g'; have h := htk c0 _ F' hFF rfl g g'; rw [← hE] at h; exact Spike.Lib.X64.WakePh.Ti2.takeOkA_tpX h
  have hFt : ∀ m pm, F' m → F' (Ret0.takeMem pm (X64WakeOSide.r1W hp i) m) :=
    Ret0.takeMem_of_kstable (a := (Ly).lab Ret0.StackTake.siteL)
      (fun s s' hk hm => hKt s s' (.inl (by rw [haW]; exact hk)) hm) (Ly).exe (Ly).endPc
  have hseg := Spike.Lib.X64.Rt.threadInit_segWAtAC (p := X64WakeT1.wakeSrc)
    (lbl := Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
    (ms := tpXa ms1 t) (F0 := F) (Ly).lays rfl hti hrc.take hF hR hRlo hhi hFF (tiQ (t2 (Ly).lab) c0 g)
    (by show (16384#64 : BitVec 64).toNat + 16384 ≤ 536870912; decide) hfld' htk'
    (P := Spike.Lib.X64Consumer.Pz (X64WakeOSide.r1W hp i)) (Spike.Lib.X64.WakePh.Ti2.pz_fstable_ti2_64 hbase)
    hTn hRS hfit hout hFt
  -- off the clone's pc `TakeK` of the site is `TakeCK`
  have hseg1 := hseg.mono_K (K' := KA)
    fun s c hw s' => by
      constructor
      · rintro (hk | ⟨hcl, -⟩)
        · rw [haW] at hk; exact hk
        · exact absurd hcl.1 hw.1.2.1.1
      · exact fun hk => .inl (by rw [haW]; exact hk)
  -- `WSX` gives `W1W` and `X1W`
  have hseg2 := hseg1.mono_W (W' := fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c [] ∧ NoSetFsAt s)
    fun s c hw => by
      refine ⟨⟨?_, Spike.Lib.X64.WakePh.Ti2.x1W_of_x0T hw.1.2.1⟩, hw.2⟩
      unfold Spike.Lib.X64.WakeOPremW.W1W Spike.Lib.X64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
      rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
      exact hw.1.2.2
  rw [← hE]
  refine hseg2.mono_post fun s c h => ?_
  obtain ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ := h
  exact ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩

end Inst

end Spike.Lib.X64.WakeTi2Hat

/-- info: 'Spike.Lib.X64.WakeTi2Hat.hti_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeTi2Hat.hti_W
