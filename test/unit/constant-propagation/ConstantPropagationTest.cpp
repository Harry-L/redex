/*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "ConstantPropagation.h"

#include <gtest/gtest.h>

#include "ConstantPropagationTestUtil.h"
#include "IRAssembler.h"

TEST(ConstantPropagation, JumpToImmediateNext) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (if-eqz v0 :next) ; This jumps to the next opcode regardless of whether
                       ; the test is true or false. So in this case we cannot
                       ; conclude that v0 == 0 in the 'true' block, since that
                       ; is identical to the 'false' block.
     (:next)
     (if-eqz v0 :end)
     (const v0 1)
     (:end)
     (return-void)
    )
)");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (load-param v0)
     (if-eqz v0 :next)
     (:next)
     (if-eqz v0 :end)
     (const v0 1)
     (:end)
     (return-void)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

TEST_F(ConstantPropagationTest, InstanceOfNull) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 0)
     (instance-of v0 "Ljava/lang/String;")
     (move-result-pseudo v1)
     (if-eqz v1 :next)
     (const v2 1)
     (goto :end)
     (:next)
     (const v2 2)
     (:end)
     (return-void)
    )
)");

  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 0)
      (const v1 0)
      (goto :next)
      (const v2 1)
      (goto :end)
      (:next)
      (const v2 2)
      (:end)
      (return-void)
    )
)");
  EXPECT_CODE_EQ(code.get(), expected_code.get());
}

// A typical case where a non-default block is uniquely reachable.
TEST(ConstantPropagation, Switch1) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (switch v0 (:b :c))
     (const v1 100)
     (return v1)

     (:b 1) ; reachable
     (const v1 200)
     (return v1)

     (:c 3) ; unreachable
     (const v1 300)
     (return v1)
  )

)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (goto :b)

     (const v1 100)
     (return v1)

     (:b) ; reachable
     (const v1 200)
     (return v1)

     (const v1 300)
     (return v1)
    )
)");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Default block also has a unreachable label.
TEST(ConstantPropagation, Switch2) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (switch v0 (:a :b :c))

     (:a 0) ; default or unreachable
     (const v1 100)
     (return v1)

     (:b 1) ; reachable
     (const v1 200)
     (return v1)

     (:c 3) ; unreachable
     (const v1 300)
     (return v1)
  )

)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (goto :b)

     (const v1 100)
     (return v1)

     (:b) ; reachable
     (const v1 200)
     (return v1)

     (const v1 300)
     (return v1)
    )
)");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Multiple unreachables labels fall into a block
TEST(ConstantPropagation, Switch3) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (switch v0 (:b :c :d))

     (const v1 100)
     (return v1)

     (:b 1) ; reachable
     (const v1 200)
     (return v1)

     (:c 3) ; unreachable
     (:d 4) ; unreachable
     (const v1 300)
     (return v1)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (goto :b)

     (const v1 100)
     (return v1)

     (:b) ; reachable
     (const v1 200)
     (return v1)

     (const v1 300)
     (return v1)
    )
)");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// When reachable and unreachable fall into a same block
TEST(ConstantPropagation, Switch4) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (switch v0 (:b :c :d))

     (const v1 100)
     (return v1)

     (:b 1) ; reachable
     (:c 3) ; unreachable
     (const v1 200)
     (return v1)

     (:d 4) ; unreachable
     (const v1 300)
     (return v1)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 1)
     (goto :b)

     (const v1 100)
     (return v1)

     (:b) ; reachable
     (const v1 200)
     (return v1)

     (const v1 300)
     (return v1)
    )
)");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Except default block, all are unreachable
// Switch is just deleted.
TEST(ConstantPropagation, Switch5) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 3)
     (switch v0 (:b :d))

     (const v1 100)
     (return v1)

     (:b 1) ; unreachable
     (const v1 200)
     (return v1)

     (:d 4) ; unreachable
     (const v1 300)
     (return v1)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 3)

     (const v1 100)
     (return v1)

     (const v1 200)
     (return v1)

     (const v1 300)
     (return v1)
    )
)");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Except default block with a switch target, all are unreachable.
// Switch is just deleted.
TEST(ConstantPropagation, Switch6) {
  auto code = assembler::ircode_from_string(R"(
    (
     (const v0 2)
     (switch v0 (:a :b :d))

     (:a 2)
     (const v1 100)
     (return v1)

     (:b 1) ; unreachable
     (const v1 200)
     (return v1)

     (:d 4) ; unreachable
     (const v1 300)
     (return v1)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
     (const v0 2)

     (const v1 100)
     (return v1)

     (const v1 200)
     (return v1)

     (const v1 300)
     (return v1)
    )
)");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// A uniquely non-default case with constant.
TEST(ConstantPropagation, SwitchOnExactConstant) {
  auto code = assembler::ircode_from_string(R"(
    (
      (const v0 1)
      (switch v0 (:b))
      ; unreachable
      (const v1 100)
      (return v1)

      (:b 1) ; reachable
      (const v1 200)
      (return v1)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (const v0 1)
      (goto :b)
      ; unreachable
      (const v1 100)
      (return v1)

      (:b) ; reachable
      (const v1 200)
      (return v1)
    )
)");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

TEST(ConstantPropagation, SwitchOnInterval) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (if-gez v0 :a)
      (const v0 0)
      (:a)
      ; at this point, we know v0 is >= 0

      (switch v0 (:b))
      ; reachable
      (const v1 100)
      (return v1)
      (:b 1) ; reachable
      (const v1 200)
      (return v1)
    )
)");

  auto original = assembler::to_s_expr(code.get());
  do_const_prop(code.get());

  EXPECT_EQ(assembler::to_s_expr(code.get()), original) << show(code.get());
}

// A uniquely non-default case with non-constant.
// Do not optimize this since default is reachable.
TEST(ConstantPropagation, Switch8) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (switch v0 (:b))
      ; reachable
      (const v1 100)
      (return v1)

      (:b 1) ; reachable
      (const v1 200)
      (return v1)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (switch v0 (:b))
      ; reachable
      (const v1 100)
      (return v1)

      (:b 1) ; reachable
      (const v1 200)
      (return v1)
    )
)");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

// Remove dead switch if no non-default block exists.
TEST(ConstantPropagation, Switch9) {
  auto code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (switch v0  (:a :b))
      (:b 1) ; reachable
      (:a 2) ;
      (const v1 200)
      (return v1)
    )
)");
  do_const_prop(code.get());

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (load-param v0)
      (const v1 200)
      (return v1)
    )
)");

  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

TEST(ConstantPropagation, WhiteBox1) {
  auto code = assembler::ircode_from_string(R"( (
     (load-param v0)

     (const v1 0)
     (const v2 1)
     (move v3 v1)
     (if-eqz v0 :if-true-label)

     (const v2 0)
     (if-gez v0 :if-true-label)

     (:if-true-label)
     (return-void)
    )
)");

  code->build_cfg(/* editable */ false);
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();
  cp::intraprocedural::FixpointIterator intra_cp(
      cfg, cp::ConstantPrimitiveAnalyzer());
  intra_cp.run(ConstantEnvironment());

  auto exit_state = intra_cp.get_exit_state_at(cfg.exit_block());
  // Specifying `0u` here to avoid any ambiguity as to whether it is the null
  // pointer
  EXPECT_EQ(exit_state.get<SignedConstantDomain>(0u),
            SignedConstantDomain::top());
  EXPECT_EQ(exit_state.get<SignedConstantDomain>(1), SignedConstantDomain(0));
  // v2 can contain either the value 0 or 1
  EXPECT_EQ(exit_state.get<SignedConstantDomain>(2),
            SignedConstantDomain(sign_domain::Interval::GEZ));
  EXPECT_EQ(exit_state.get<SignedConstantDomain>(3), SignedConstantDomain(0));
}

TEST(ConstantPropagation, WhiteBox2) {
  auto code = assembler::ircode_from_string(R"(
    (
     (load-param v0)

     (:loop)
     (const v1 0)
     (if-gez v0 :if-true-label)
     (goto :loop)
     ; if we get here, that means v0 >= 0

     (:if-true-label)
     (return-void)
    )
)");

  code->build_cfg(/* editable */ false);
  auto& cfg = code->cfg();
  cfg.calculate_exit_block();
  cp::intraprocedural::FixpointIterator intra_cp(
      cfg, cp::ConstantPrimitiveAnalyzer());
  intra_cp.run(ConstantEnvironment());

  auto exit_state = intra_cp.get_exit_state_at(cfg.exit_block());
  EXPECT_EQ(exit_state.get<SignedConstantDomain>(0u),
            SignedConstantDomain(sign_domain::Interval::GEZ));
  EXPECT_EQ(exit_state.get<SignedConstantDomain>(1), SignedConstantDomain(0));
}
