/**
 * Copyright (c) 2016-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

#include "ConstantPropagation.h"

#include <gtest/gtest.h>

#include "Creators.h"
#include "ConstantPropagationTestUtil.h"
#include "IRAssembler.h"

struct EnumTest : public ConstantPropagationTest {
 public:
  EnumTest() {
    ClassCreator creator(get_enum_type());
    creator.set_super(get_object_type());
    auto equals = static_cast<DexMethod*>(DexMethod::make_method(
        "Ljava/lang/Enum;.equals:(Ljava/lang/Object;)Z"));
    equals->make_concrete(ACC_PUBLIC | ACC_FINAL, true);
    creator.add_method(equals);
    creator.create();
  }

  static DexClass* create_enum() {
    auto cls_ty = DexType::make_type("LFoo;");
    ClassCreator creator(cls_ty);
    creator.set_super(get_enum_type());
    creator.set_access(ACC_PUBLIC | ACC_FINAL | ACC_ENUM);

    auto enum_x = static_cast<DexField*>(DexField::make_field("LFoo;.X:I"));
    auto enum_y = static_cast<DexField*>(DexField::make_field("LFoo;.Y:I"));
    enum_x->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL | ACC_ENUM);
    enum_y->make_concrete(ACC_PUBLIC | ACC_STATIC | ACC_FINAL | ACC_ENUM);
    creator.add_field(enum_x);
    creator.add_field(enum_y);
    return creator.create();
  }
};

TEST_F(EnumTest, ReferencesEqual) {
  Scope scope{create_enum()};

  auto code = assembler::ircode_from_string(R"(
    (
      (sget-object "LFoo;.X:I")
      (move-result-pseudo-object v0)
      (sget-object "LFoo;.X:I")
      (move-result-pseudo-object v1)
      (if-eq v0 v1 :if-true-label)
      (const v0 0)
      (:if-true-label)
      (const v0 1)
      (return v0)
    )
)");

  using EnumAnalyzer =
      InstructionSubAnalyzerCombiner<cp::EnumFieldSubAnalyzer,
                                     cp::ConstantPrimitiveSubAnalyzer>;

  do_const_prop(code.get(), [analyzer = EnumAnalyzer()](auto* insn, auto* env) {
    analyzer.run(insn, env);
  });

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (sget-object "LFoo;.X:I")
      (move-result-pseudo-object v0)
      (sget-object "LFoo;.X:I")
      (move-result-pseudo-object v1)
      (goto :if-true-label)
      (const v0 0)
      (:if-true-label)
      (const v0 1)
      (return v0)
    )
)");
  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

TEST_F(EnumTest, ReferencesNotEqual) {
  Scope scope{create_enum()};

  auto code = assembler::ircode_from_string(R"(
    (
      (sget-object "LFoo;.X:I")
      (move-result-pseudo-object v0)
      (sget-object "LFoo;.Y:I")
      (move-result-pseudo-object v1)
      (if-ne v0 v1 :if-true-label)
      (const v0 0)
      (:if-true-label)
      (const v0 1)
      (return v0)
    )
)");

  using EnumAnalyzer =
      InstructionSubAnalyzerCombiner<cp::EnumFieldSubAnalyzer,
                                     cp::ConstantPrimitiveSubAnalyzer>;

  do_const_prop(code.get(), [analyzer = EnumAnalyzer()](auto* insn, auto* env) {
    analyzer.run(insn, env);
  });

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (sget-object "LFoo;.X:I")
      (move-result-pseudo-object v0)
      (sget-object "LFoo;.Y:I")
      (move-result-pseudo-object v1)
      (goto :if-true-label)
      (const v0 0)
      (:if-true-label)
      (const v0 1)
      (return v0)
    )
)");
  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}

TEST_F(EnumTest, EqualsMethod) {
  Scope scope{create_enum()};

  auto code = assembler::ircode_from_string(R"(
    (
      (sget-object "LFoo;.X:I")
      (move-result-pseudo-object v0)
      (sget-object "LFoo;.Y:I")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "LFoo;.equals:(Ljava/lang/Object;)Z")
      (move-result v0)
      (if-eqz v0 :if-true-label)
      (const v0 0)
      (:if-true-label)
      (const v0 1)
      (return v0)
    )
)");

  using EnumAnalyzer =
      InstructionSubAnalyzerCombiner<cp::EnumFieldSubAnalyzer,
                                     cp::ConstantPrimitiveSubAnalyzer>;

  do_const_prop(code.get(), [analyzer = EnumAnalyzer()](auto* insn, auto* env) {
    analyzer.run(insn, env);
  });

  auto expected_code = assembler::ircode_from_string(R"(
    (
      (sget-object "LFoo;.X:I")
      (move-result-pseudo-object v0)
      (sget-object "LFoo;.Y:I")
      (move-result-pseudo-object v1)
      (invoke-virtual (v0 v1) "LFoo;.equals:(Ljava/lang/Object;)Z")
      (move-result v0)
      (goto :if-true-label)
      (const v0 0)
      (:if-true-label)
      (const v0 1)
      (return v0)
    )
)");
  EXPECT_EQ(assembler::to_s_expr(code.get()),
            assembler::to_s_expr(expected_code.get()));
}