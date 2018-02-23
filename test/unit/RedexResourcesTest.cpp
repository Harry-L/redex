/**
 * Copyright (c) 2016-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

#include <map>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <gtest/gtest.h>

#include "Debug.h"
#include "RedexResources.h"
#include "androidfw/ResourceTypes.h"

std::set<std::string> values_to_set(
  const std::unordered_multimap<std::string, std::string>& map,
  const std::string& key) {
  std::set<std::string> result;
  auto range = map.equal_range(key);
  for (auto it = range.first; it != range.second; ++it) {
    result.emplace(it->second);
  }
  return result;
}

TEST(RedexResources, ReadXmlTagsAndAttributes) {
  std::unordered_set<std::string> attributes_to_find;
  attributes_to_find.emplace("android:onClick");
  attributes_to_find.emplace("onClick");
  attributes_to_find.emplace("android:text");

  std::unordered_set<std::string> classes;
  std::unordered_multimap<std::string, std::string> attribute_values;

  collect_layout_classes_and_attributes_for_file(
    std::getenv("test_layout_path"),
    attributes_to_find,
    classes,
    attribute_values);

  EXPECT_EQ(classes.size(), 3);
  EXPECT_EQ(classes.count("Lcom/example/test/CustomViewGroup;"), 1);
  EXPECT_EQ(classes.count("Lcom/example/test/CustomTextView;"), 1);
  EXPECT_EQ(classes.count("Lcom/example/test/CustomButton;"), 1);

  auto vals = values_to_set(attribute_values, "android:onClick");
  EXPECT_EQ(vals.size(), 2);
  EXPECT_EQ(vals.count("fooClick"), 1);
  EXPECT_EQ(vals.count("barClick"), 1);

  auto text_vals = values_to_set(attribute_values, "android:text");
  EXPECT_EQ(text_vals.size(), 4);

  auto no_ns_vals = values_to_set(attribute_values, "onClick");
  EXPECT_EQ(no_ns_vals.size(), 0);
}
