#include "hashtables/bucket.h"
#include "hashtables/probing.h"
#include "hashtables/std_unordered_map.h"

#include "hashers/const_hash.h"
#include "hashers/std_hash.h"

#include "hasher.h"
#include "hashtable.h"
#include "gtest/gtest.h"

#include <functional>

using namespace std;

using HashTables = ::testing::Types<
    HashMap::Buckets<int, int, Hash::STD<int>>,
    HashMap::STD<int, int, Hash::STD<int>>,
    HashMap::Probing<int, int, HashMap::Probes::Linear<int, Hash::STD<int>, 1>>,
    HashMap::Probing<int, int,
                     HashMap::Probes::Linear<int, Hash::Const<int>, 1>>,
    HashMap::Probing<int, int,
                     HashMap::Probes::Quadratic<int, Hash::STD<int>>>>;

template <class HashTable> class HashTableTests : public testing::Test {};

TYPED_TEST_SUITE(HashTableTests, HashTables);

TYPED_TEST(HashTableTests, InitiallyEmpty) {
  TypeParam hashmap;
  EXPECT_EQ(hashmap.size(), 0);
  EXPECT_FALSE(hashmap.find(-1));
  EXPECT_FALSE(hashmap.find(0));
}

TYPED_TEST(HashTableTests, CanInsertUniqueKeys) {
  TypeParam hashmap;
  EXPECT_TRUE(hashmap.insert(3, 3));
  EXPECT_EQ(hashmap.size(), 1);
  EXPECT_FALSE(hashmap.insert(3, 4));
  EXPECT_EQ(hashmap.size(), 1);
}

TYPED_TEST(HashTableTests, CanEraseElements) {
  TypeParam hashmap;
  EXPECT_TRUE(hashmap.insert(3, 3));
  EXPECT_EQ(hashmap.size(), 1);
  EXPECT_TRUE(hashmap.erase(3));
  EXPECT_EQ(hashmap.size(), 0);
}

TYPED_TEST(HashTableTests, CanFindElements) {
  int k = 3;
  int v = 3;
  TypeParam hashmap;
  EXPECT_TRUE(hashmap.insert(k, v));
  int *value = hashmap.find(k);
  EXPECT_TRUE(value);
  EXPECT_EQ(*value, v);
}

TYPED_TEST(HashTableTests, ManyInsertsAndErase) {
  // intended to test resize
  TypeParam hashmap;
  const auto max = 1 << 16;
  for (auto i = 0; i < max; i++)
    EXPECT_TRUE(hashmap.insert(i, max - i));
  for (auto i = 0; i < max; i++) {
    int *val = hashmap.find(i);
    EXPECT_TRUE(val);
    EXPECT_EQ(*val, max - i);
  };
  for (auto i = 0; i < max; i++)
    EXPECT_TRUE(hashmap.erase(i));
  EXPECT_EQ(hashmap.size(), 0);
}
