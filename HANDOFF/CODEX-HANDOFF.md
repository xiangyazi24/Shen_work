# CODEX HANDOFF — Shen_work χ₀=0 capstone, the Tower campaign
(written 2026-06-10 ~15:45 by Zinan/Claude; latest commit at writing: 3799b11)

## 你接手时的第一件事
1. `git log --oneline -5` 看是否有比 3799b11 更新的提交(一个 stage-1 agent
   可能在我之后落地了四个新文件,见 §Stage1;若 git status 有未提交的
   IntervalDuhamelSourceShift.lean 等四文件,先验证再提交)。
2. 读 `HANDOFF/chatgpt-tower-verdict.md`(塔总设计,外审过)和
   `HANDOFF/horizon-retype-status.md` 头部(战役总台账)。

## 当前状态(全部已验证、已推送)
- capstone `paper2_theorem_1_1_chiZero_unconditional`
  (ShenWork/Paper2/IntervalDomainThm11ChiZeroCoreProvider.lean) 签名:
  regime 常数 (χ₀=0, a>0, b>0, α≥1, γ≥1) + HWdata
  (∀ u₀ PID, ∀ D, D.u = picardLimit p u₀ D.T → WdataProvider p u₀ D)。
- `#print axioms` capstone = [propext, sorryAx, Classical.choice, Quot.sound]。
- sorryAx 唯一来源:`hinterior`(IntervalPicardLimitSliceTimeContinuity.lean
  内 mildSlice_restart_bound 的内部段)。
- 全仓库其余 0 sorry。全量 lake build 8544 jobs 绿。
- HWdata 与 hinterior 同根:都卡在"逐迭代源包生产塔"。塔成齐闭。

## 硬规则(违反任何一条 = 返工)
1. 绝不引入 axiom。绝不把 sorry 换成更弱的陈述。axiom 不是可接受的逃生口。
2. 绝不在本地跑 `lake build`(24GB mini 会 kernel panic;有 block 脚本拦)。
   远程验证流程:
   rsync -az <file> uisai2:/dev/shm/shen_work/<path>   (绝不 --delete)
   ssh uisai2 'export PATH="$HOME/.elan/bin:$PATH" && cd /dev/shm/shen_work
     && lake env lean <file>'
   依赖 olean 旧了就 `lake build ShenWork.<module>`(远程)。
   最终验收:远程全量 lake build + 对 capstone 跑 #print axioms。
3. Mathlib v4.29.1 改名陷阱:abs_add→abs_add_le;gcongr 常分解错,用显式
   add_le_add / mul_le_mul_of_nonneg_left;无 unfold_let(用 show+unfold);
   lt_of_not_le→lt_of_not_ge;Function.update_same→update_self。
4. 证不过先查定义(Proof Stuck = Bug)。本战役抓过的同类病:全局量词
   不可满足、零延拓全局 C²、∀x 形分裂恒等式、σ≥0 全局衰减——见各
   HANDOFF/chatgpt-*-verdict.md。遇到"假设疑似不可满足"时:构造反例探针
   验证,然后 retype 成可满足形,绝不硬填。
5. 提交规范:小步提交,信息里写清杀了什么/留了什么/为什么;只 push
   已全量验证的状态。

## Stage 1(可能已由并行 agent 落地——先查)
四个新文件,塔判决条目 1-10:
- IntervalDuhamelSourceShift.lean: shift_nonneg(10行)、
  duhamelSpectralCoeff_congr_on_Icc、localRestartCoeff_congr_on_Icc
- IntervalPicardIterateRestartLocal.lean: ShiftedSourceWitness 定义 +
  hbsum/hagree_succ_of_shiftedWitness + hagree_succ_of_subtypeCont
  (修 lift-连续性陷阱)
- IntervalPicardIterateC2BoundLocal.lean: iterate_abs_deriv2_le_of_shiftedWitness
- IntervalPicardIterateTimeC1Full.lean: K1 全包(补 hadotcont 腿)+
  clampedIterateSource_duhamelSourceTimeC1(钳制迭代源,镜像
  IntervalDomainClampedSourceRepresentation 的 w∘Φ 重索引技巧)

## Stage 2(塔本体,判决条目 11-16)
- IntervalPicardSourceTower.lean: TowerLevel 载体(照判决:repr 水平局部 +
  K2 profile + srcWin 窗口见证;不带 K1、不带原始全局 TimeC1)、
  tower_zero(n=0 用零源 restart 在 offset=lo/2,绕 s=0 墙)、
  tower_succ(半步见证←srcWin(t/2,t)+shift;repr n+1 用见证变体;
  K2 n+1 用 deriv2 见证变体 + g2_step_closes;srcWin n+1 用 K1 全包 +
  源生产器 + 软钳制)、tower_all。
- IntervalPicardTowerProjection.lean: wdata_all_of_tower(直接填
  IterateWindowC2Data,别绕 wdata_all_of_wiring)、
  (奖励) limitBddOn_inputs_of_tower——它关 hinterior:极限侧 BddOn
  生产者的输入从塔投影,然后 hinterior 走谱重启路
  (picardLimitRestart_general_of_subtypeCont + 级数相减,设计见
  HANDOFF/chatgpt-hslicetc-verdict.md 和 IntervalPicardLimitSliceTimeContinuity
  的 docstring)。
- 终接线:hresCore_of_tower → capstone 的 HWdata 卸载 → #print axioms
  应只剩 [propext, Classical.choice, Quot.sound]。

## 锥侧已暴露的数据(实例化点可直接用)
coneGradientMildSolutionData_exists_with_gate_data
(IntervalMildPicardConeData)返回:D.T=δ、D.u=picardLimit(精确函数等式)、
GateCondition p D.M A₂ D.T(已解!exists_gate_solution 在
IntervalPicardGateSolve)、∀n HasContinuousSlices、PicardConvFacts、
∀n 严格迭代正性。塔的 step 假设里 ball/正性/gate 全部从这里喂。

## 外审判决索引(全在 HANDOFF/,做事前读对应那份)
- chatgpt-tower-verdict.md ——塔设计(本战役的执行图纸)
- chatgpt-final-wiring-verdict.md ——锥内选小 δ vs EqOn 收缩
- chatgpt-hslicetc-verdict.md ——hinterior 的固定基点路线
- chatgpt-r2-hybrid-verdict.md + chatgpt-r2-second-opinion.md ——
  混合带权 C²(已执行)
- chatgpt-final-wave-verdict.md ——迭代表示疗法 + Leibniz(已执行)
- chatgpt-capstone-audit-verdict.md ——假设链审计(无隐藏空洞)
- hdu-threading-design.md / hsrc0-splitenv-design.md ——历史设计

## 与 ChatGPT 协作(可选)
~/repos/chatgpt-bridge/ask-chatgpt.sh --channel cron(或 cron2)--stdin。
问前必须 commit+push(GitHub connector 才能读到)。设计级问题先送审
再执行,本战役 6 份判决 3 次抓出真错误,值得。
