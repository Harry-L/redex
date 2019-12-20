/*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redex.test.instr;

import static org.fest.assertions.api.Assertions.assertThat;

import org.junit.Test;

public class LoopInvariantCodeMotionTest {

  @Test
  public void test() {
    int j = 0;
    for (int i = 0; i < 10; i++) {
      j = i;
      System.out.println("foo");
    }
    assertThat(j == 9);
  }
}
