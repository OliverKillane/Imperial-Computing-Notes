#include "hashtables/bucket.h"
#include "hashtables/std_unordered_map.h"
#include "hashtables/probing.h"

#include "hashtable.h"
#include "hasher.h"

#include "gtest/gtest.h"

#include <functional>

using namespace std;

using HashTables = ::testing::Types<
    BucketMap<int, int, std_hash<int>>,
    STLUnorderedMap<int, int>,
    ProbingHashMap<int, int, Probes::Linear<int, std_hash<int>>>,
    ProbingHashMap<int, int, Probes::Quadratic<int, std_hash<int>>>
>;

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
    int* value = hashmap.find(k);
    EXPECT_TRUE(value);
    EXPECT_EQ(*value, v);
}

TYPED_TEST(HashTableTests, ManyInsertsAndErase) {
    // intended to test resize
    TypeParam hashmap;
    const auto max = 1 << 16;
    for (auto i = 0; i < max; i ++) EXPECT_TRUE(hashmap.insert(i, max - i));
    for (auto i = 0; i < max; i ++) {
        int* val = hashmap.find(i);
        EXPECT_TRUE(val);
        EXPECT_EQ(*val, max - i);
    };
    for (auto i = 0; i < max; i ++) EXPECT_TRUE(hashmap.erase(i));
    EXPECT_EQ(hashmap.size(), 0);
}
