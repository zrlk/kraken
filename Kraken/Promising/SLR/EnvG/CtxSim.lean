/-
Whole-thread environment (`EnvG`): the **context-level simulation** between the actual context of an
instruction and the environment's context for the same access.

ISA-neutral. The environment runs every access on a context with the actual
memory and promise set, its own (lower) views, the instruction-local fields at
their defaults, and instruction views `0` (`zeroIv`). This file relates the two
contexts with the Sim library at `ρ = idUpTo |M|` (no foreign messages: the
memories are equal) and transports every actual outcome of an event to an
environment outcome with the same value and timestamp:

- `CtxLe iv cx cxe`: `Sim.SimInv (idUpTo |cx.mem|) 0 ⊥ iv (envIv iv) cx cxe`
  plus equal memories and promise sets;
- `CtxLe.read` (`Sim.SimInv.read`), `CtxLe.fence` (`Sim.SimInv.fence`),
  `CtxLe.fenceOpt` (`Sim.SimInv.fenceOpt`), `CtxLe.post` (`Sim.SimInv.post`),
  `CtxLe.rmwAfter`, `CtxLe.xclFail`;
- `CtxLe.write`: the write simulation at `ρ = idUpTo`, with the map after a
  fresh write again an `idUpTo` (`freshMap_idUpTo`), built from
  `Sim.afterWrite_rel`, `Sim.CtxRel.fresh` and `Sim.writePre_le`; the same
  write event (`WriteEv`) on both sides;
- `CtxLe.overtaken` (an environment-overtaken write is actually overtaken),
  `CtxLe.wfloor` (the environment's floor is lower: `RStep.mono`),
  `CtxLe.views_le` (plain `≤` on every view).

`envIv iv` has the shape of `iv` (`dataPer` of the same length, so that
`Sim.IVLe` holds) and every view `0`; the rules read only the five scalar
fields, so it runs exactly as `zeroIv` (`readSuccs_envIv`, `writeSuccs_envIv`).
-/
import Kraken.Promising.SLR.Sim.Instances
import Kraken.Promising.SLR.ThreadRuleX

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## The environment's instruction views -/

/-- The instruction views the environment runs every access with: all `0`
(no register views are tracked). -/
def zeroIv : InstrViews := { addrR := 0, addrW := 0, dataR := 0, dataW := 0, condW := 0 }

/-- `zeroIv` shaped like `iv` (`dataPer` of the same length, every entry
`(0, 0)`), so that `Sim.IVLe ρ (envIv iv) iv` holds. Runs as `zeroIv`. -/
def envIv (iv : InstrViews) : InstrViews := { zeroIv with dataPer := iv.dataPer.map fun _ => (0, 0) }

theorem ivLe_envIv (ρ : TMap) (iv : InstrViews) : IVLe ρ (envIv iv) iv := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, ?_⟩
  show Rel2 _ (iv.dataPer.map fun _ => ((0 : View), (0 : View))) iv.dataPer
  generalize iv.dataPer = ps
  induction ps with
  | nil => exact .nil
  | cons p ps ih => exact .cons ⟨Nat.zero_le _, Nat.zero_le _⟩ ih

/-- The environment's store views: `forStore` does not change `envIv`. -/
theorem envIv_forStore (iv : InstrViews) (i : Nat) : (envIv iv).forStore i = envIv iv := by
  unfold InstrViews.forStore
  split
  · rename_i a b h
    have : (a, b) = ((0 : View), (0 : View)) := by
      simp only [envIv, List.getElem?_map] at h
      cases e : iv.dataPer[i]? with
      | none => rw [e] at h; cases h
      | some _ => rw [e] at h; exact (Option.some.inj h).symm
    cases this
    rfl
  · rfl

theorem envIv_le (iv : InstrViews) (n : Nat) : (envIv iv).Le n := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun p hp => ?_⟩
  simp only [envIv, List.mem_map] at hp
  obtain ⟨_, -, rfl⟩ := hp
  exact ⟨Nat.zero_le _, Nat.zero_le _⟩

/-- The read rule reads only the scalar fields of the instruction views. -/
theorem readSuccs_envIv (A : Arch) (iv : InstrViews) : readSuccs A (envIv iv) = readSuccs A zeroIv := rfl

/-- The write rule reads only the scalar fields of the instruction views. -/
theorem writeSuccs_envIv (A : Arch) (tid : Nat) (iv : InstrViews) :
    writeSuccs A tid (envIv iv) = writeSuccs A tid zeroIv := rfl

/-! ## `idUpTo` after a fresh write -/

theorem TMap.ext' {a b : TMap} (h1 : a.dom = b.dom) (h2 : a.f = b.f) (h3 : a.fv = b.fv) : a = b := by
  cases a; cases b; simp only at h1 h2 h3; subst h1 h2 h3; rfl

/-- A fresh write at the end of two equally long memories extends `idUpTo |M|`
to `idUpTo (|M| + 1)`. -/
theorem freshMap_idUpTo {M M' : Memory} (hm : MemRel (TMap.idUpTo M.last) M M') (hl : M'.last = M.last) :
    freshMap (TMap.idUpTo M.last) hm = TMap.idUpTo (M.last + 1) := by
  apply TMap.ext'
  · funext s
    show (s ≤ M.last ∨ s = M.last + 1) = (s ≤ M.last + 1)
    apply propext; (try simp only [Time] at *) <;> omega
  · funext s
    show (if s = M.last + 1 then M'.last + 1 else s) = s
    split <;> ((try simp only [Time] at *) <;> omega)
  · funext v
    show (if M.last + 1 ≤ v then M'.last + 1 else min v M.last) = min v (M.last + 1)
    split <;> ((try simp only [Time, View] at *) <;> omega)

/-! ## The relation -/

/-- **The context relation** between the actual context `cx` of an
instruction with views `iv` and the environment's context `cxe` for the same
access: the Sim invariant at `ρ = idUpTo |M|` with no foreign messages, equal
memories and promise sets (and so views `cxe ≤ cx`). -/
structure CtxLe (iv : InstrViews) (cx cxe : Ctx) : Prop where
  sim : SimInv (TMap.idUpTo cx.mem.last) 0 (fun _ => False) iv (envIv iv) cx cxe
  mem : cxe.mem = cx.mem
  prom : cxe.prom = cx.prom

theorem idUpTo_fv_le (n v : Nat) : (TMap.idUpTo n).fv v ≤ v := Nat.min_le_left _ _

/-- No foreign messages: the target memory is the source memory. -/
theorem noForeign_idUpTo (M : Memory) : NoForeign (TMap.idUpTo M.last) M :=
  fun s' _ h2 => ⟨s', h2, rfl⟩

/-- Plain `≤` on every view, from `ViewsLe` at `idUpTo`. -/
structure ViewsLeP (vs' vs : Views) : Prop where
  coh : ∀ l, vs'.getCoh l ≤ vs.getCoh l
  vrNew : vs'.vrNew ≤ vs.vrNew
  vrOld : vs'.vrOld ≤ vs.vrOld
  vrOldNR : vs'.vrOldNR ≤ vs.vrOldNR
  vwNew : vs'.vwNew ≤ vs.vwNew
  vwOld : vs'.vwOld ≤ vs.vwOld
  vwOldNT : vs'.vwOldNT ≤ vs.vwOldNT
  vCAP : vs'.vCAP ≤ vs.vCAP
  vRel : vs'.vRel ≤ vs.vRel

theorem viewsLeP_of {n : Nat} {vs' vs : Views} (h : ViewsLe (TMap.idUpTo n) vs' vs) : ViewsLeP vs' vs :=
  ⟨fun l => Nat.le_trans (h.coh l) (idUpTo_fv_le _ _), Nat.le_trans h.vrNew (idUpTo_fv_le _ _),
   Nat.le_trans h.vrOld (idUpTo_fv_le _ _), Nat.le_trans h.vrOldNR (idUpTo_fv_le _ _),
   Nat.le_trans h.vwNew (idUpTo_fv_le _ _), Nat.le_trans h.vwOld (idUpTo_fv_le _ _),
   Nat.le_trans h.vwOldNT (idUpTo_fv_le _ _), Nat.le_trans h.vCAP (idUpTo_fv_le _ _),
   Nat.le_trans h.vRel (idUpTo_fv_le _ _)⟩

namespace CtxLe

variable {A : Arch} {tid : Nat} {iv : InstrViews} {cx cxe : Ctx}

theorem views_le (h : CtxLe iv cx cxe) : ViewsLeP cxe.views cx.views := viewsLeP_of h.sim.rel.views

/-- The environment's write floor is at most the actual one. -/
theorem wfloor (h : CtxLe iv cx cxe) : cxe.views.wfloor ≤ cx.views.wfloor := by
  have := h.views_le
  simp only [Views.wfloor]
  exact max_le_max' this.vwNew this.vCAP

/-- **Dead branches transfer**: an environment-overtaken context is
actually overtaken (same promises and memory, lower `coh`). -/
theorem overtaken (h : CtxLe iv cx cxe) (ho : cxe.Overtaken) : cx.Overtaken := by
  obtain ⟨p, hp, w, hw, hle⟩ := ho
  rw [h.prom] at hp
  rw [h.mem] at hw
  exact ⟨p, hp, w, hw, Nat.le_trans hle (h.views_le.coh w.loc)⟩

/-- Re-anchor `CtxLe` to an equal memory. -/
theorem congrMem {cx₁ cxe₁ : Ctx} (hs : SimInv (TMap.idUpTo cx.mem.last) 0 (fun _ => False) iv (envIv iv) cx₁ cxe₁)
    (hm : cx₁.mem = cx.mem) (hme : cxe₁.mem = cx₁.mem) (hp : cxe₁.prom = cx₁.prom) : CtxLe iv cx₁ cxe₁ :=
  ⟨hm ▸ hs, hme, hp⟩

/-- **Read transport** (`Sim.SimInv.read`): every actual read outcome is an
environment read outcome (instruction views `zeroIv`) from the same
timestamp with the same value, and the relation continues. -/
theorem read (h : CtxLe iv cx cxe) {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {tr : Time} {v : Val}
    {cx₁ : Ctx} (hx : (tr, v, cx₁) ∈ readSuccs A iv cx k xcl l noRet) :
    ∃ cxe₁, (tr, v, cxe₁) ∈ readSuccs A zeroIv cxe k xcl l noRet ∧ CtxLe iv cx₁ cxe₁ := by
  obtain ⟨cxe₁, hx', hs, hm⟩ := h.sim.read A hx (fun hf => hf.elim)
  have e1 := readSuccs_memProm A _ hx
  have e2 := readSuccs_memProm A _ hx'
  refine ⟨cxe₁, hx', congrMem hs hm ?_ ?_⟩
  · simp only at e1 e2; rw [e2.1, e1.1, h.mem]
  · simp only at e1 e2; rw [e2.2, e1.2, h.prom]

theorem fence (h : CtxLe iv cx cxe) (k : FenceKind) : CtxLe iv (fenceStep cx k) (fenceStep cxe k) :=
  congrMem (h.sim.fence k) (fenceStep_mem cx k) (by rw [fenceStep_mem, fenceStep_mem, h.mem])
    (by rw [fenceStep_prom, fenceStep_prom, h.prom])

theorem fenceOpt (h : CtxLe iv cx cxe) : CtxLe iv (fenceOptCtx A cx) (fenceOptCtx A cxe) := by
  unfold fenceOptCtx; split
  · exact h.fence .sy
  · exact h

theorem post (h : CtxLe iv cx cxe) (k : RmwKind) (noRet : Bool) (l : Loc) :
    CtxLe iv (rmwPost A k noRet l cx) (rmwPost A k noRet l cxe) := by
  have hp : ∀ c : Ctx, (rmwPost A k noRet l c).prom = c.prom := fun c => by unfold rmwPost; split <;> rfl
  exact congrMem (h.sim.post A k noRet l) (rmwPost_mem A k noRet l cx)
    (by rw [rmwPost_mem, rmwPost_mem, h.mem]) (by rw [hp, hp, h.prom])

theorem rmwAfter (h : CtxLe iv cx cxe) (k : RmwKind) (noRet : Bool) (l : Loc) :
    CtxLe iv (rmwAfter A k noRet l cx) (rmwAfter A k noRet l cxe) := by
  unfold SLR.rmwAfter; split
  · exact (h.post k noRet l).fence .sy
  · exact h.post k noRet l

theorem xclFail (h : CtxLe iv cx cxe) (l : Loc) : CtxLe iv (xclFailCtx cx l) (xclFailCtx cxe l) := by
  have hv := h.sim.rel.views
  refine ⟨⟨⟨h.sim.rel.mem, ⟨hv.coh, hv.vrNew, hv.vrOld, hv.vrOldNR, hv.vwNew, hv.vwOld, hv.vwOldNT, hv.vCAP,
      hv.vRel, hv.fwd, trivial⟩, h.sim.rel.prom, h.sim.rel.loadViews, Nat.zero_le _, h.sim.rel.rmwWrote,
      h.sim.rel.stores⟩, ⟨h.sim.bnd.views.xclbNone, h.sim.bnd.loadViews, Nat.zero_le _⟩, h.sim.promDom,
      h.sim.domAll, h.sim.ivr, h.sim.ivb, h.sim.nle, h.sim.fgn⟩, h.mem, h.prom⟩

/-- Build `CtxLe` from the relation at `idUpTo |M|` and the actual-side bounds. -/
theorem mk' (hr : CtxRel (TMap.idUpTo cx.mem.last) cx cxe) (hb : cx.Bnd) (hp : ∀ s ∈ cx.prom, s ≤ cx.mem.last)
    (hivb : iv.Le cx.mem.last) (hm : cxe.mem = cx.mem) (hpr : cxe.prom = cx.prom) : CtxLe iv cx cxe :=
  ⟨⟨hr, hb, hp, fun _ h => h, ivLe_envIv _ iv, hivb, Nat.zero_le _,
    hm ▸ NoForeign.fgnSep (noForeign_idUpTo cx.mem) 0 _⟩, hm, hpr⟩

/-- **Re-target `CtxLe`** to a context that agrees with the target on every
field the relation reads (views, promises, memory and the
instruction-local fields; not `promisedNow` or the log). -/
theorem congrT (h : CtxLe iv cx cxe) {cxe' : Ctx} (hv : cxe'.views = cxe.views) (hp : cxe'.prom = cxe.prom)
    (hm : cxe'.mem = cxe.mem) (hl : cxe'.loadViews = cxe.loadViews) (hs : cxe'.succView = cxe.succView)
    (hw : cxe'.rmwWrote = cxe.rmwWrote) (hst : cxe'.stores = cxe.stores) : CtxLe iv cx cxe' := by
  obtain ⟨⟨⟨r1, r2, r3, r4, r5, r6, r7⟩, hb, hpd, hda, hivr, hivb, hnle, hfgn⟩, hme, hpe⟩ := h
  refine ⟨⟨⟨hm ▸ r1, hv ▸ r2, hp ▸ r3, hl ▸ r4, hs ▸ r5, hw ▸ r6, hst ▸ r7⟩, hb, hpd, hda, hivr, hivb, hnle,
    hm ▸ hfgn⟩, hm ▸ hme, hp ▸ hpe⟩

/-- **The relation at an instruction's start**: the actual context with
views `vs`, promises `p` and memory `M` (bounded by `|M|`, the instruction
views too), the environment's with views `vs' ≤ vs` at `idUpTo |M|`, the same
promises and memory, and every instruction-local field at its default. -/
theorem start {vs vs' : Views} {p : List Time} {M : Memory} {lg lg' : List TraceEv}
    (hv : ViewsLe (TMap.idUpTo M.last) vs' vs) (hb : vs.Bnd M.last) (hp : ∀ s ∈ p, s ≤ M.last)
    (hiv : iv.Le M.last) :
    CtxLe iv { views := vs, prom := p, mem := M, log := lg } { views := vs', prom := p, mem := M, log := lg' } := by
  have hb' : Ctx.Bnd { views := vs, prom := p, mem := M, log := lg } :=
    ⟨hb, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
  refine mk' ⟨(CtxRel.memExt hb' hp (Memory.Prefix.refl M)).mem, hv, PromRel.self_idUpTo hp, .nil,
    Nat.zero_le _, rfl, rfl⟩ hb' hp hiv rfl rfl

/-- A write event depends only on the memories and promise sets. -/
theorem _root_.Kraken.Promising.SLR.WriteEv.congr {cx cx' cy cy' : Ctx} {l : Loc} {v : Val} {tr : Option Time}
    {tw : Time} (h : WriteEv tid cx cx' l v tr tw) (hm : cy.mem = cx.mem) (hp : cy.prom = cx.prom)
    (hm' : cy'.mem = cx'.mem) (hp' : cy'.prom = cx'.prom) : WriteEv tid cy cy' l v tr tw := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, by rw [hp', hp]; exact h2, by rw [hm]; exact h3⟩
  rw [hm', hm, hp]; exact h1

/-- The exclusive-read timestamp of a store: the same in both contexts. -/
theorem xclTr (h : CtxLe iv cx cxe) (xcl : Bool) :
    (if xcl then cxe.views.xclb.map (·.1) else none) = (if xcl then cx.views.xclb.map (·.1) else none) := by
  cases xcl
  · rfl
  · have hx := h.sim.rel.views.xclb
    simp only [↓reduceIte]
    revert hx
    rcases cx.views.xclb with _ | ⟨a, b, l1⟩ <;> rcases cxe.views.xclb with _ | ⟨a', b', l2⟩ <;>
      simp only [XclLe, Option.map, imp_self, false_implies]
    rintro ⟨-, rfl, -, -⟩; rfl

/-- **Write transport** at `ρ = idUpTo |M|` (`Sim.afterWrite_rel`,
`Sim.CtxRel.fresh`, `Sim.writePre_le`, `freshMap_idUpTo`): every actual write
outcome (instruction views `ivs`, extra data view `extra`) is an environment
write outcome (views `ivs' ≤ ivs`, `extra' ≤ extra`) with the same write event,
and the relation continues. -/
theorem write (h : CtxLe iv cx cxe) (hi : cx.Inv tid) {ivs ivs' : InstrViews}
    (hivs : IVLe (TMap.idUpTo cx.mem.last) ivs' ivs) (hivsb : ivs.Le cx.mem.last) {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra extra' : View} (hex : extra' ≤ extra) (hexb : extra ≤ cx.mem.last)
    {xr : View} {cx₂ : Ctx} (hc : cx₂ ∈ writeSuccs A tid ivs cx k xcl l v tr extra xr) :
    ∃ cxe₂ tw, cxe₂ ∈ writeSuccs A tid ivs' cxe k xcl l v tr extra' ∧ WriteEv tid cx cx₂ l v tr tw ∧
      WriteEv tid cxe cxe₂ l v tr tw ∧ CtxLe iv cx₂ cxe₂ := by
  have hv := h.sim.rel.views
  have hex' : extra' ≤ (TMap.idUpTo cx.mem.last).fv extra := by
    show extra' ≤ min extra cx.mem.last; omega_t
  have hpre := Sim.writePre_le A hivs hv k hex'
  have hB : max (writePre A ivs' cxe k extra') (cxe.views.getCoh l) ≤
      max (writePre A ivs cx k extra) (cx.views.getCoh l) :=
    Nat.le_trans (le_fv_max hpre (hv.coh l)) (idUpTo_fv_le _ _)
  have hfwd : max ivs'.addrR (max ivs'.dataR extra') ≤
      (TMap.idUpTo cx.mem.last).fv (max ivs.addrR (max ivs.dataR extra)) :=
    le_fv_max hivs.addrR (le_fv_max hivs.dataR hex')
  obtain ⟨hb2, -⟩ := writeSuccs_bnd A tid ivs h.sim.bnd hivsb hexb hc
  obtain ⟨hi2, -⟩ := writeSuccs_inv A tid ivs hc hi
  have hp2 : ∀ s ∈ cx₂.prom, s ≤ cx₂.mem.last := fun s hs => by
    obtain ⟨w, hw, -⟩ := hi2.prom s hs
    exact (get?_some_le hw).2
  obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid ivs hc hi
  suffices hex : ∃ cxe₂, cxe₂ ∈ writeSuccs A tid ivs' cxe k xcl l v tr extra' ∧
      CtxRel (TMap.idUpTo cx₂.mem.last) cx₂ cxe₂ ∧ cxe₂.mem = cx₂.mem ∧ cxe₂.prom = cx₂.prom by
    obtain ⟨cxe₂, hc', hr, hm, hp⟩ := hex
    exact ⟨cxe₂, tw, hc', hev, hev.congr h.mem h.prom hm hp,
      mk' hr hb2 hp2 (h.sim.ivb.mono (writeSuccs_bnd A tid ivs h.sim.bnd hivsb hexb hc).2) hm hp⟩
  rcases (mem_writeSuccs A tid).mp hc with ⟨t, htp, w, hw, hl, hvv, htid, ⟨hok1, hok2⟩, rfl⟩ |
    ⟨⟨hok1, hok2⟩, rfl⟩
  · -- fulfil the same promise
    have ht : (TMap.idUpTo cx.mem.last).dom t := h.sim.promDom t htp
    refine ⟨_, (mem_writeSuccs A tid).mpr (.inl ⟨t, h.prom ▸ htp, w, by rw [h.mem]; exact hw, hl, hvv, htid,
      ⟨Nat.lt_of_le_of_lt hB hok1, fun a ha => by rw [h.mem]; exact hok2 a ha⟩, rfl⟩),
      Sim.afterWrite_rel A h.sim.rel hivs.addrW _ xcl l v ht hfwd true true (Nat.zero_le _), h.mem, ?_⟩
    show cxe.prom.erase t = cx.prom.erase t
    rw [h.prom]
  · -- a fresh write at the end of both (equal) memories
    have hml : cxe.mem.last = cx.mem.last := by rw [h.mem]
    have hc2 := Sim.CtxRel.fresh h.sim.rel h.sim.bnd h.sim.promDom { loc := l, val := v, tid }
      (pn := cx.promisedNow ++ [({ loc := l, val := v, tid }, max (writePre A ivs cx k extra) (cx.views.getCoh l))])
      (pn' := cxe.promisedNow ++
        [({ loc := l, val := v, tid }, max (writePre A ivs' cxe k extra') (cxe.views.getCoh l))])
    rw [freshMap_idUpTo h.sim.rel.mem hml] at hc2
    have hiv2 : ivs'.addrW ≤ (TMap.idUpTo (cx.mem.last + 1)).fv ivs.addrW := by
      have h1 := hivs.addrW; have := hivsb.addrW
      show _ ≤ min ivs.addrW (cx.mem.last + 1)
      change _ ≤ min ivs.addrW cx.mem.last at h1; omega_t
    have hfwd2 : max ivs'.addrR (max ivs'.dataR extra') ≤
        (TMap.idUpTo (cx.mem.last + 1)).fv (max ivs.addrR (max ivs.dataR extra)) := by
      have := hivsb.addrR; have := hivsb.dataR
      show _ ≤ min (max ivs.addrR (max ivs.dataR extra)) (cx.mem.last + 1)
      change _ ≤ min (max ivs.addrR (max ivs.dataR extra)) cx.mem.last at hfwd; omega_t
    have hd : (TMap.idUpTo (cx.mem.last + 1)).dom (cx.mem.last + 1) := Nat.le_refl _
    have hr := Sim.afterWrite_rel A hc2 hiv2 (A.storeKind k) xcl l v hd hfwd2 false false (xr := xr) (Nat.zero_le _)
    have hlast : (cx.mem.append { loc := l, val := v, tid }).1.last = cx.mem.last + 1 :=
      Memory.last_append _ _
    refine ⟨_, (mem_writeSuccs A tid).mpr (.inr ⟨⟨Nat.lt_of_le_of_lt hB (by rw [hml]; exact hok1), ?_⟩, rfl⟩),
      ?_, ?_, ?_⟩
    · intro a ha; rw [h.mem]; exact hok2 a ha
    · show CtxRel (TMap.idUpTo (cx.mem.append { loc := l, val := v, tid }).1.last) _ _
      rw [hlast, ← hml]
      rw [hml] at hr ⊢
      exact hr
    · show (cxe.mem.append { loc := l, val := v, tid }).1 = (cx.mem.append { loc := l, val := v, tid }).1
      rw [h.mem]
    · show (cxe.prom ++ [cxe.mem.last + 1]).erase (cxe.mem.last + 1) =
        (cx.prom ++ [cx.mem.last + 1]).erase (cx.mem.last + 1)
      rw [h.prom, hml]

end CtxLe

end Kraken.Promising.SLR.EnvG
