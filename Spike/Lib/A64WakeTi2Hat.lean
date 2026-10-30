/-
**`HMidP.ti`'s discharger** (AArch64; `A64WakeHMid.HMidP.ti`): wake's second
`scc_rt_thread_init` call, from `wc_main` on the second TCB `t2` returning to
`.sp6`, is a segment inside `W1X ∧ NoMsrAt` under `h1`'s outside move
`TakeCK aW r1W ClW`, at `tpXa ms1 t`, its post the stack `r1W` in private
memory.

`Rt.threadInit_segWA` at `r1Of` (`q.k0 = 16384`), its node obligations
`Ti2.ti2_WS` (inside `StartWf.WS` at `X0T`, the start's level instantiated
at `W1W`'s arena, source, clone and placement) lifted to `NoMsrAt`
(`Ti2.tiW_nm`); `WS` gives `W1W` (the marks by `AbOffW.marks_target`) and
`X1W` (`x1W_of_x0T`); the take `TakeK` is `TakeCK`'s off the clone's pc
(`SegW.mono_K`).

The callee's frame on the pool and `r1W` off it come from `BoxPure`'s base
(`hbase`: `bandP_box`, `hout_box`, `hRS_box`), main's stack owned at the
site (`owned_r0`) from the box's frame off `R` (`hF0`, `StackOff`), the
call's frame (in `R` off the callee's region), the take's frame (`R'`'s
cells off the take's region: `TiW`'s `.call` `CallerCells`, via `ti2_WS`'s
`hXs`) and the take's cells, `R`'s bounds 8-aligned (`hR8`). Left as named
premises:
the second TCB's words (`hmF`, `hunF`, `hnoF`, `hoffT`), the counters off
the arena (`hoffL`, `hoffX`), the sources' facts (`hSctl`, `hpl`; no `CFacts`:
the runtime's nodes are proved at a dummy control, `Ti2C0`),
the field and take facts (`hfld`, `htk`), `hF0`. The child's stack unowned
before its take comes from the pre's `Pz r1W` (`x0T_sitePz`), kept by the
callee's frames (`pz_fstable_ti2`).

- `hti_W`: `HMidP.ti` (with `SB` at `c0`).

No absolute address appears in this file.
-/
import Spike.Lib.A64WakeHMid
import Spike.Lib.A64WakeTi2W
import Spike.Lib.A64WakeTiNoMsr
import Spike.Lib.A64WakeTi2HatG
import Spike.Lib.A64WakeTi2Box
import Spike.Lib.A64SiteOfPlaceW
import Spike.Lib.A64WakeAbOffW
import Spike.Lib.A64WakeSrcCtl
import Spike.Lib.A64WakeTi2Slot
import Spike.Lib.A64WakeTi2R0

namespace Spike.Lib.WakeTi2Hat

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.WakeWc (t2 tiQ clonePc stOk_tpXa)
open Spike.Lib.A64.WakePh.WcSp4 (wcNI)
open Spike.Lib.A64.WakePh.Tcb2Call (oW)
open Spike.Lib.A64.Flow.Ret0 (tiN tiX StackM)
open Spike.Lib.A64.KeepTP (NoMsrAt tpXa)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakeLoadT (L0T ls0T tcb0)
open Spike.Lib.WakeBoxW (W1X)
open Spike.Lib.WakeHMid (SB)
open Spike.Lib.A64ConsumerA (TakeCK)
open Spike.Lib.A64.WakePh.Ti2 (BandP X0T)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Spike.Lib.A64Consumer.Lsize)
  (l : WeakMem.AllocLabel) (b n : Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => WakeH1Inv.ms1W hp i E cT ls0 l b n []

set_option maxHeartbeats 3200000 in
/-- **`HMidP.ti` at `R`, `F`, `t`**: from the layout's program wake's
(`hpg`, `hlo`, `hpa`), the take site at `scc_rt_take_site` (`haW`), the
words' separation (`hs`) and the named premises of the file's header, at
the pre `Pz r1W`; `BoxPure`'s base `hbase`. -/
theorem hti_W {R : Region} {F : MachineData → Prop} {t : UInt64} (hpg : o.prog = wakeProg)
    (hlo : (Ly).Λ.code.lo = Spike.Lib.A64.WakePh.lo) (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    (haW : WakeOSide.aW hp i E = (Ly).lab Ret0.StackTake.siteL)
    (hs : Spike.Lib.A64.WakePh.WSep (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab))
    (hro : (Ly).Λ.rodata.Disjoint (Ly).Λ.stackPool)
    (hSctl : ∀ l' A c, SB l b l' A c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf WakeT1.wakeSrc c [])
    (hpl : ∀ c0, (∃ l' A', SB l b l' A' c0) → ∀ s : State,
      placeVal (machine (kernel 1)) s (.slot (R.addr (-72)).toNat) = some b →
      placeVal (machine (kernel 1)) s (.slot (R.addr (-80)).toNat) = some (tcb0 (Ly).Λ) →
      Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ (A64ConsumerA.upd (L0T (Ly).Λ) l b) s c0 [])
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m)
    (hmF : ∀ a ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (t2 (Ly).lab),
      Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) true ⟨a, 8⟩ = true)
    (hunF : ∀ a ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (t2 (Ly).lab), ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hnoF : ∀ a ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (t2 (Ly).lab), ∀ j w,
      (⟨a, 8⟩, w) ∉ Spike.Lib.A64.WakePh.own2b (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) j)
    (hoffT : ∀ a ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (t2 (Ly).lab),
      ¬ ((WakeOD.arW hp i).heap ≤ a.toNat ∧ a.toNat < (WakeOD.arW hp i).heap + 16 * (WakeOD.arW hp i).cells) ∧
      (⟨a, 8⟩ : Loc) ≠ (WakeOD.arW hp i).ctrLoc)
    (hoffL : ¬ ((WakeOD.arW hp i).heap ≤ (Ly).lockA.toNat ∧
        (Ly).lockA.toNat < (WakeOD.arW hp i).heap + 16 * (WakeOD.arW hp i).cells) ∧
      (⟨(Ly).lockA, 8⟩ : Loc) ≠ (WakeOD.arW hp i).ctrLoc)
    (hoffX : ¬ ((WakeOD.arW hp i).heap ≤ (Ly).nextA.toNat ∧
        (Ly).nextA.toNat < (WakeOD.arW hp i).heap + 16 * (WakeOD.arW hp i).cells) ∧
      (⟨(Ly).nextA, 8⟩ : Loc) ≠ (WakeOD.arW hp i).ctrLoc)
    (hbase : R.base.toNat + 48 = (Ly).stacksA.toNat + 16384) (hRs : R.lo ≤ -336 ∧ 0 ≤ R.hi)
    (hR8 : R.lo % 8 = 0 ∧ R.hi % 8 = 0)
    (hsub : (WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool)
    (hF0 : ∀ m, F m → Ret0.StackOff (Spike.Lib.A64.Rt.Ti2.r0Of (Ly).lab) R m)
    (hfld : ∀ e ∈ Ret0.ThreadInit.fields (t2 (Ly).lab) (Ret0.stacksA (Ly).lab + 16384#64),
      Ret0.StOk ms1 F (Ly).exe (WakeSpawnR.endR hp i) (t2 (Ly).lab + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
      R' = R.callee (-80) (-256) 0 → ∀ (g : Ret0.ThreadInit.G) (g' : Ret0.StackTake.G),
      Spike.Lib.A64.Rt.TakeOkA ms1 F (Ly).exe (WakeSpawnR.endR hp i) (R'.callee (-48) (-208) 0) F'
        (Ret0.tiTake (tiQ (t2 (Ly).lab) c0 g) g')) :
    ∀ (c0 : Ctl), (∃ l' A', SB l b l' A' c0) → ∀ (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (R' : Region)
      (F' : MachineData → Prop), cA.toNat = b → m.toNat = tcb0 (Ly).Λ →
      R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 → 0 ≤ R'.hi → FStable R' F' →
      KStable (TakeCK (WakeOSide.aW hp i E) (WakeOSide.r1W hp i) (WakeOD.ClW hp i)) F' → (∀ m, F' m → F m) →
      R' = R.callee (-80) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -80) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNI (Ly).lab c0 (t2 (Ly).lab) cA m fr).J σC c ∧
          (tiN (Ly).lab (tiQ (t2 (Ly).lab) c0 g) .e).J (enter (-80) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oW mC σC ∧ (wcNI (Ly).lab c0 (t2 (Ly).lab) cA m fr).J σC c ∧
          (tiN (Ly).lab (tiQ (t2 (Ly).lab) c0 g) .e).J (enter (-80) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -80) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (fun s c => W1X hp i E Dt Ctx ls0 l b n s c [] ∧ NoMsrAt s)
          (TakeCK (WakeOSide.aW hp i E) (WakeOSide.r1W hp i) (WakeOD.ClW hp i)) WakeT1.wakeSrc
          (A64ConsumerA.upd (L0T (Ly).Λ) l b) (tpXa ms1 t)
          (fun s c => At (Ly).exe (WakeSpawnR.endR hp i) R' F' (tiN (Ly).lab (tiQ (t2 (Ly).lab) c0 g) .e) s c ∧
            Spike.Lib.A64Consumer.Pz (WakeOSide.r1W hp i) s.st.1)
          (fun s c => ∃ x, At (Ly).exe (WakeSpawnR.endR hp i) R' F' (tiX (Ly).lab (tiQ (t2 (Ly).lab) c0 g) x) s c ∧
            StackM (WakeOSide.r1W hp i) s.st.1) := by
  intro c0 hSB cA m fr R' F' hcA hmw hR hal hRlo hhi hF hKt hFF hR' hCC g hpre hFm
  subst hR'
  have hbd : BandP (Ly) R (-336) := Spike.Lib.A64.WakePh.Ti2.bandP_box hbase
  have hfit := Spike.Lib.A64.Rt.fitS_of_sub (Ly) hsub
  have hout := Spike.Lib.A64.WakePh.Ti2.hout_box (L := Ly) hbase
  have hRS := Spike.Lib.A64.WakePh.Ti2.hRS_box (L := Ly) hbase
  have hlab : ∀ l x, Scc.Cert.Link.A64.codeOf Spike.Lib.A64.WakePh.lo wakeProg l = some x →
      (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hp i l x (by rw [hlo, hpg]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hp)
  have hsite := Spike.Lib.PlaceW.site_ofPlaceW hp i
  have hpL : (Ly).prog = wakeProg := hpg
  have hE : (Ly).endPc = WakeSpawnR.endR hp i := by
    show Scc.Cert.Rt.A64.endOf _ (Ly).prog _ = _; rw [hpL]
  have hrc : Spike.Lib.A64.Rt.RtCodeIn0 (Ly).prog := hpL ▸ Spike.Lib.A64.WakePh.wake_rtCodeIn0
  obtain ⟨l', A', hS⟩ := hSB
  have hc := hSctl _ _ _ hS
  -- the return address `.sp6`, from the caller's node
  have hra : g.ra = ((Ly).lab ".L21_wc_main.sp6").toBitVec := by
    obtain ⟨σC, c, hw, -, -, -, hx, -⟩ := hpre
    exact hx.symm.trans hw.2.2.1
  -- the take's frame and `r1W`'s stability
  have hSM := Ret0.stackM_stable hfit hout
  have hSMt : FStable ((R.callee (-80) (-256) 0).callee Ret0.ThreadInit.oI.sp (-208) 0)
      (StackM (WakeOSide.r1W hp i)) := by
    refine Ret0.stackM_stable hfit fun a h8 ha ha7 => ?_
    show (a : Int) + 8 ≤ (((R.callee (-80) (-256) 0).callee (-48) (-208) 0).base.toNat : Int) + -208 ∨
      (((R.callee (-80) (-256) 0).callee (-48) (-208) 0).base.toNat : Int) + 0 ≤ a
    have hb' := Region.callee_base (hi' := 0) hR (show (R.callee (-80) (-256) 0).lo ≤ -48 + -208 by omega)
      (by decide) (show (-48 : Int) < (R.callee (-80) (-256) 0).hi by omega)
    rcases hout a h8 ha ha7 with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  have hal8 : R.base.toNat % 8 = 0 := by have := (Ly).stacks_al; omega
  -- main's slots at the callee's states, for the placement
  have hPlK := Spike.Lib.A64.WakePh.Ti2.slotP_keep (L := Ly) hbase ⟨by omega, hRs.2⟩ hcA hmw fun m' h =>
    let ⟨mC, σC, _, hA, hJ, _, hk⟩ := hFm m' h; ⟨mC, σC, hA, hJ.2.2.2.2.1, hJ.2.2.2.2.2.1, hk⟩
  -- the nodes inside `WS` at `X0T`, then at `NoMsrAt`
  have hT := Spike.Lib.A64.WakePh.StartTi.ti2_WS (P := Spike.Lib.A64Consumer.Pz (WakeOSide.r1W hp i))
    (L := Ly) (a := Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
    (rS := WakeOSide.r1W hp i) (ar := WakeOD.arW hp i) (p := WakeT1.wakeSrc) (Dt := Dt) (Cl := WakeOD.ClW hp i)
    (Ctx := fun _ _ _ => False) (lbl := A64ConsumerA.upd (L0T (Ly).Λ) l b)
    (lsize := A64ConsumerA.updN (ls0T ls0) l n) (frM := ⟨"", c0.term, c0.env, [], .int⟩)
    (X0 := X0T (Ly) (WakeOSide.aW hp i E))
    hpL hlo hlab hsite (fun _ h => h.2) hc
    (fun s h => (Spike.Lib.A64.WakePh.Ti2.slotP_place h).elim (hpl c0 ⟨l', A', hS⟩ s)) hPlK
    (Spike.Lib.A64.WakePh.Ti2.x0T_ti hlab haW)
    (Spike.Lib.A64.WakePh.Ti2.bandP_callee hbd (by decide) (by decide)) hΛ hs hro hR hal hRlo hhi
    (fun m h => hFr m (hFF m h)) (tiQ (t2 (Ly).lab) c0 g) rfl hmF (fun a ha m h => hunF a ha m (hFF m h)) hnoF
    hra rfl hsub hSM hSMt
    hoffT hoffL hoffX
    (fun s hpc hr hm hz h4 h3 => Spike.Lib.A64.WakePh.Ti2.x0T_sitePz
      (fun h => Spike.Lib.WakeSrcCtl.cloneAt_ne_site hp i hpg h.symm)
      (P := fun s => Ret0.CallerCells (R.callee (-80) (-256) 0) (-48) (-208) 0 s.st.1 ∧
        ∀ k, ((R.callee (-80) (-256) 0).callee (-48) (-208) 0).Off k →
          (Mem.loadInt s.st.1.dmem (((R.callee (-80) (-256) 0).callee (-48) (-208) 0).addr k) 8).isSome)
      (fun s _ _ hm h4 => Spike.Lib.A64.WakePh.Ti2.owned_r0 hbase hal8 hR8 hRs (hF0 _ (hFF _ hm)) (hCC _ hm)
        h4.1 h4.2) s hpc hr hm hz ⟨h4, h3⟩)
  have hTn := Spike.Lib.A64.WakePh.Ti2.tiW_nm (Ly).lays rfl hrc.ti hrc.take hT
  -- the segment, at `TakeK` of the site
  have hfld' : ∀ e ∈ Ret0.ThreadInit.fields (t2 (Ly).lab) (Ret0.stacksA (Ly).lab + 16384#64),
      Ret0.StOk (tpXa ms1 t) F (Ly).exe (Ly).endPc (t2 (Ly).lab + BitVec.ofNat 64 e.1) e.2 := by
    intro e he; have h := hfld e he; rw [← hE] at h; exact stOk_tpXa h
  have htk' : ∀ g', Spike.Lib.A64.Rt.TakeOkA (tpXa ms1 t) F (Ly).exe (Ly).endPc
      ((R.callee (-80) (-256) 0).callee (-48) (-208) 0) F' (Ret0.tiTake (tiQ (t2 (Ly).lab) c0 g) g') := by
    intro g'; have h := htk c0 _ F' hFF rfl g g'; rw [← hE] at h; exact Spike.Lib.A64.WakePh.Ti2.takeOkA_tpX h
  have hFt : ∀ m pm, F' m → F' (Ret0.takeMem pm (WakeOSide.r1W hp i) m) :=
    Ret0.takeMem_of_kstable (a := (Ly).lab Ret0.StackTake.siteL)
      (fun s s' hk hm => hKt s s' (.inl (by rw [haW]; exact hk)) hm) (Ly).exe (Ly).endPc
  -- the segment, at `TakeK` of the site
  have hseg := Spike.Lib.A64.Rt.threadInit_segWA (p := WakeT1.wakeSrc) (lbl := A64ConsumerA.upd (L0T (Ly).Λ) l b)
    (ms := tpXa ms1 t) (F0 := F) (Ly).lays rfl hrc.ti hrc.tiSp hrc.take hF hR hal hRlo hhi hFF (tiQ (t2 (Ly).lab) c0 g)
    (by show (16384#64 : BitVec 64).toNat + 16384 ≤ 536870912; decide) hfld' htk'
    (P := Spike.Lib.A64Consumer.Pz (WakeOSide.r1W hp i)) (Spike.Lib.A64.WakePh.Ti2.pz_fstable_ti2 hbase)
    hTn hRS hfit hout hFt
  -- off the clone's pc `TakeK` of the site is `TakeCK`
  have hseg1 := hseg.mono_K (K' := TakeCK (WakeOSide.aW hp i E) (WakeOSide.r1W hp i) (WakeOD.ClW hp i))
    fun s c hw s' => by
      constructor
      · rintro (hk | ⟨hcl, -⟩)
        · rw [haW] at hk; exact hk
        · exact absurd hcl.1 hw.1.2.1.1
      · exact fun hk => .inl (by rw [haW]; exact hk)
  -- `WS` gives `W1W` and `X1W`
  have hseg2 := hseg1.mono_W (W' := fun s c => W1X hp i E Dt Ctx ls0 l b n s c [] ∧ NoMsrAt s)
    fun s c hw => by
      refine ⟨⟨?_, Spike.Lib.A64.WakePh.Ti2.x1W_of_x0T hw.1.2.1⟩, hw.2⟩
      unfold WakeOPremW.W1W Spike.Lib.A64.WakeWf.W1 WakeOD.AbW WakeOD.AcW
      rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
      exact hw.1.2.2
  rw [← hE]
  refine hseg2.mono_post fun s c h => ?_
  obtain ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ := h
  exact ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩

end Inst

end Spike.Lib.WakeTi2Hat

/-- info: 'Spike.Lib.WakeTi2Hat.hti_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeTi2Hat.hti_W
