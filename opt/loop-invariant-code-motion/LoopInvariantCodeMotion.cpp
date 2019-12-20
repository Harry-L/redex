/*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "LoopInvariantCodeMotion.h"
#include "ControlFlow.h"
#include "DexClass.h"
#include "IRCode.h"
#include "LoopInfo.h"
#include "Pass.h"
#include "ReachingDefinitions.h"
#include "Walkers.h"

using namespace loop_impl;

std::unordered_set<cfg::Block*> get_dominators_in_loop(
    Loop* loop,
    cfg::Block* block,
    LoopInvariantCodeMotionPass::DominatorMap dominator_map) {
  std::unordered_set<cfg::Block*> dominators;

  // a block always dominates itself
  dominators.emplace(block);

  // the header block dominates every block
  auto header = loop->get_header();

  auto current_block = block;
  while (current_block != header) {
    current_block = dominator_map.at(current_block).dom;
    dominators.emplace(current_block);
  }

  return dominators;
}

std::unordered_set<cfg::Block*> get_blocks_dominating_exit_blocks(
    cfg::ControlFlowGraph& cfg,
    Loop* loop,
    LoopInvariantCodeMotionPass::DominatorMap dominator_map) {

  auto exit_blocks = loop->get_exit_blocks();

  // if there are no exit blocks, all blocks are dominating
  if (exit_blocks.size() == 0) {
    std::unordered_set<cfg::Block*> blocks;
    for (auto block : *loop) {
      blocks.emplace(block);
    }
    return blocks;
  }

  auto it = exit_blocks.begin();
  auto intersection_block = *it;
  for (++it; it != exit_blocks.end(); ++it) {
    intersection_block =
        cfg.idom_intersect(dominator_map, intersection_block, *it);
  }

  return get_dominators_in_loop(loop, intersection_block, dominator_map);
}

struct Use {
  IRInstruction* insn;
  reg_t reg;
  bool operator==(const Use&) const;
};

bool Use::operator==(const Use& that) const {
  return insn == that.insn && reg == that.reg;
}

namespace std {

template <>
struct hash<Use> {
  size_t operator()(const Use& use) const {
    size_t seed = boost::hash<IRInstruction*>()(use.insn);
    boost::hash_combine(seed, use.reg);
    return seed;
  }
};

} // namespace std

using Def = IRInstruction*;
using UDChains = std::unordered_map<Use, sparta::PatriciaTreeSet<Def>>;
using DUChains = std::unordered_map<Def, std::unordered_set<Use>>;
using InstructionBlock = std::unordered_map<IRInstruction*, cfg::Block*>;

void calculate_chains(const cfg::ControlFlowGraph& cfg,
                      UDChains& ud_chains,
                      DUChains& du_chains,
                      InstructionBlock& insn_block,
                      std::unordered_set<IRInstruction*>& kills_other_def) {
  reaching_defs::FixpointIterator fixpoint_iter{cfg};
  fixpoint_iter.run(reaching_defs::Environment());

  for (cfg::Block* block : cfg.blocks()) {
    reaching_defs::Environment defs_in =
        fixpoint_iter.get_entry_state_at(block);
    for (const auto& mie : InstructionIterable(block)) {
      auto insn = mie.insn;
      insn_block.emplace(insn, block);
      for (size_t i = 0; i < insn->srcs_size(); ++i) {
        auto src = insn->src(i);
        Use use{insn, src};
        auto defs = defs_in.get(src);
        always_assert_log(!defs.is_top() && defs.size() > 0,
                          "Found use without def when processing [0x%lx]%s",
                          &mie, SHOW(insn));
        ud_chains[use] = defs.elements();
        for (auto def : defs.elements()) {
          du_chains[def].insert(use);
        }
      }
      if (insn->has_dest()) {
        auto dest = insn->dest();
        auto defs = defs_in.get(dest);
        if (!defs.is_top() && (defs.size() > 1 || !defs.elements().contains(insn))) {
          kills_other_def.emplace(insn);
          TRACE(LOOP, 3, "insn %s kill", show(insn).c_str());
        } else {
          if (defs.is_top()) {
            TRACE(LOOP, 3, "insn %s does not kill other def bc top", show(insn).c_str());
          } else {
            TRACE(LOOP, 3, "insn %s does not kill other def bc size %d", show(insn).c_str(), defs.size());
          }

        }
      }
      fixpoint_iter.analyze_instruction(insn, &defs_in);
    }
  }
}

cfg::Block* idom_intersect(
    const std::unordered_map<cfg::Block*, cfg::DominatorInfo>& postorder_dominator,
    cfg::Block* block1,
    cfg::Block* block2) {
  auto finger1 = block1;
  auto finger2 = block2;
  while (finger1 != finger2) {
    while (postorder_dominator.at(finger1).postorder <
           postorder_dominator.at(finger2).postorder) {
      finger1 = postorder_dominator.at(finger1).dom;
    }
    while (postorder_dominator.at(finger2).postorder <
           postorder_dominator.at(finger1).postorder) {
      finger2 = postorder_dominator.at(finger2).dom;
    }
  }
  return finger1;
}

// Uses a standard depth-first search ith a side table of already-visited nodes.
std::vector<cfg::Block*> blocks_post_helper(bool reverse, cfg::Block* head, std::unordered_set<cfg::Block*> blocks_to_add) {
  std::stack<cfg::Block*> stack;
  stack.push(head);

  std::vector<cfg::Block*> postorder;
  std::unordered_set<cfg::Block*> visited;
  while (!stack.empty()) {
    const auto& curr = stack.top();
    visited.insert(curr);
    bool all_succs_visited = [&] {
      for (auto const& s : curr->succs()) {
        if (blocks_to_add.count(s->target()) == 0) {
          continue;
        }
        if (!visited.count(s->target())) {
          stack.push(s->target());
          return false;
        }
      }
      return true;
    }();
    if (all_succs_visited) {
      redex_assert(curr == stack.top());
      postorder.push_back(curr);
      stack.pop();
    }
  }
  if (reverse) {
    std::reverse(postorder.begin(), postorder.end());
  }
  return postorder;
}

// Finding immediate dominator for each blocks in ControlFlowGraph.
// Theory from:
//    K. D. Cooper et.al. A Simple, Fast Dominance Algorithm.
std::unordered_map<cfg::Block*, cfg::DominatorInfo> immediate_dominators(std::vector<cfg::Block*>& postorder_blocks, std::unordered_set<cfg::Block*>& block_set) {
  // Get postorder of blocks and create map of block to postorder number.
  std::unordered_map<cfg::Block*, cfg::DominatorInfo> postorder_dominator;
  for (size_t i = 0; i < postorder_blocks.size(); ++i) {
    postorder_dominator[postorder_blocks[i]].postorder = i;
  }

  // Initialize immediate dominators. Having value as nullptr means it has
  // not been processed yet.
  for (cfg::Block* block : postorder_blocks) {
    postorder_dominator[block].dom = nullptr;
  }
  postorder_dominator[postorder_blocks.back()].dom = postorder_blocks.back();

  bool changed = true;
  while (changed) {
    changed = false;
    // Traverse block in reverse postorder.
    for (auto rit = postorder_blocks.rbegin(); rit != postorder_blocks.rend();
         ++rit) {
      cfg::Block* ordered_block = *rit;
      if (ordered_block == postorder_blocks.back()) {
        continue;
      }
      cfg::Block* new_idom = nullptr;
      // Pick one random processed block as starting point.
      for (auto& pred : ordered_block->preds()) {
        if (block_set.count(pred->src()) == 0) {
          continue;
        }
        if (postorder_dominator[pred->src()].dom != nullptr) {
          new_idom = pred->src();
          break;
        }
      }
      always_assert(new_idom != nullptr);
      for (auto& pred : ordered_block->preds()) {
        if (block_set.count(pred->src()) == 0) {
          continue;
        }
        if (pred->src() != new_idom &&
            postorder_dominator[pred->src()].dom != nullptr) {
          new_idom = idom_intersect(postorder_dominator, new_idom, pred->src());
        }
      }
      if (postorder_dominator[ordered_block].dom != new_idom) {
        postorder_dominator[ordered_block].dom = new_idom;
        changed = true;
      }
    }
  }
  return postorder_dominator;
}

LoopInvariantCodeMotionPass::Stats LoopInvariantCodeMotionPass::hoist(
    DexMethod* method) {
  auto code = method->get_code();
  if (method->is_external() || !code) {
    // method is external or abstract, nothing to do here
    return Stats();
  }

  code->build_cfg();
  auto& cfg = code->cfg();

  TRACE(LOOP, 3, show(method).c_str());

  LoopInfo loop_info(cfg);

  UDChains ud_chains;
  DUChains du_chains;
  InstructionBlock insn_block;
  std::unordered_set<IRInstruction*> kills_other_def;
  calculate_chains(cfg, ud_chains, du_chains, insn_block, kills_other_def);

  /* if (show(method) == "Lorg/junit/runners/parameterized/BlockJUnit4ClassRunnerWithParameters;.some_string:(Ljava/util/List;)V") { */
  /*   reaching_defs::FixpointIterator fixpoint_iter{cfg}; */
  /*   fixpoint_iter.run(reaching_defs::Environment()); */
  /*   for (auto block : cfg.blocks()) { */
  /*     TRACE(LOOP, 3, "block: %d", block->id()); */
  /*     reaching_defs::Environment defs_in = */
  /*       fixpoint_iter.get_entry_state_at(block); */
  /*     auto reg = defs_in.get(0); */
  /*     std::ostringstream ss; */
  /*     ss << reg; */
  /*     TRACE(LOOP, 3, ss.str().c_str()); */
  /*   } */

  /* } */

  for (auto it = loop_info.rbegin(); it != loop_info.rend(); ++it) {
    auto loop = *it;

    auto blocks_to_consider = loop->get_blocks();
    auto exits = loop->get_exit_blocks();
    for (auto block : exits) {
      blocks_to_consider.emplace_back(block);
    }
    std::unordered_set<cfg::Block*> blocks_to_add;
    for (auto block : blocks_to_consider) {
      blocks_to_add.emplace(block);
    }

    // TRACE(LOOP, 3, show(cfg).c_str());

    for (auto block : blocks_to_consider) {
      TRACE(LOOP, 3, "blocks to consider: %d", block->id());
    }

    auto postorder = blocks_post_helper(false, blocks_to_consider.front(), blocks_to_add);

    for (auto block: postorder) {
      TRACE(LOOP, 3, "postorder: %d", block->id());
    }

    always_assert(postorder.back() == loop->get_header());
    TRACE(LOOP, 3, "hello");

    auto dominator_map = immediate_dominators(postorder, blocks_to_add);

    // only hoist from blocks that dominate all exit blocks
    auto dominating_blocks =
        get_blocks_dominating_exit_blocks(cfg, loop, dominator_map);

    auto preheader = loop->get_preheader();

    for (auto block : dominating_blocks) {
      if (loop_info.get_loop_for(block) != loop) {
        continue;
      }
      std::vector<cfg::InstructionIterator> hoistable;
      for (auto& mie : InstructionIterable(block)) {
        auto insn = mie.insn;

        // only consider const instructions for now
        if (insn->opcode() != OPCODE_CONST) {
          continue;
        }

        if (kills_other_def.count(insn)) {
          continue;
        }

        // get all uses of the definition
        auto& uses = du_chains.at(insn);

        // make sure that all of the uses do not have any other definitions
        // inside of the loop
        bool only_one_def = true;
        for (auto use : uses) {
          auto& defs = ud_chains.at(use);
          for (auto d : defs) {
            if (d == insn) {
              continue;
            }
            if (loop->contains(insn_block.at(d))) {
              only_one_def = false;
              break;
            }
          }
        }
        if (!only_one_def) {
          continue;
        }

        // mark that this instruction as hoistable, and move it out of the loop
        hoistable.emplace_back(block->to_cfg_instruction_iterator(mie));
        insn_block[insn] = preheader;
      }
      if (hoistable.size() > 0) {
        TRACE(LOOP, 3, "HOIST BLOCK");
        TRACE(LOOP, 3, show(block).c_str());
        for (auto ii : hoistable) {
          TRACE(LOOP, 3, show(ii->insn).c_str());
        }
      }
      for (auto ii: hoistable) {
        block->remove_insn(ii);
        preheader->push_back(ii->insn);
      }
    }

    if (!preheader->empty()) {
      TRACE(LOOP, 3, "preheader: ");
      TRACE(LOOP, 3, show(preheader).c_str());
      TRACE(LOOP, 3, "cfg: ");
      auto str = show(cfg);
      str.erase(std::remove(str.begin(), str.end(), '%'), str.end());
      str.erase(std::remove(str.begin(), str.end(), '\\'), str.end());
      TRACE(LOOP, 3, str.c_str());

    }
  }

  code->clear_cfg();
  return Stats();
}

void LoopInvariantCodeMotionPass::run_pass(DexStoresVector& stores,
                                           ConfigFiles&,
                                           PassManager& mgr) {
  const auto scope = build_class_scope(stores);
  walk::methods(scope, hoist);
}

static LoopInvariantCodeMotionPass s_pass;
