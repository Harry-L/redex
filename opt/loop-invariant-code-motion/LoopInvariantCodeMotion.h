/*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#pragma once

#include "LoopInfo.h"
#include "Pass.h"

class LoopInvariantCodeMotionPass : public Pass {
 public:
  using DominatorMap = std::unordered_map<cfg::Block*, cfg::DominatorInfo>;
  struct Stats {
    size_t instructions_hoisted{0};
    Stats& operator+=(const Stats& that) {
      instructions_hoisted += that.instructions_hoisted;
      return *this;
    }
  };
  LoopInvariantCodeMotionPass() : Pass("LoopInvariantCodeMotionPass") {}
  void run_pass(DexStoresVector& stores,
                ConfigFiles& conf,
                PassManager& mgr) override;
  static Stats hoist(DexMethod* method);
};
