
#include "bitmap.h"
#include "bitmaps/bitvector.h"

#include "gtest/gtest.h"

using BitMapImpls = ::testing::Types<
    BitMap::BVec
>;

template <class BitMapImpl> class BitMapTests : public testing::Test {};

TYPED_TEST_SUITE(BitMapTests, BitMapImpls);

TYPED_TEST(BitMapTests, InitiallyEmpty) {
    TypeParam bmap;
    EXPECT_FALSE(bmap.get(0));
    EXPECT_FALSE(bmap.get(100'000));
}


TYPED_TEST(BitMapTests, GetReturnsSet) {
    TypeParam bmap;
    // set to true
    EXPECT_TRUE(bmap.set(0, true));
    EXPECT_TRUE(bmap.get(0));

    // set back to false
    EXPECT_TRUE(bmap.set(0, false));
    EXPECT_FALSE(bmap.get(0));

    // and for large values
    EXPECT_TRUE(bmap.set(50'000, true));
    EXPECT_TRUE(bmap.get(50'000));
    EXPECT_TRUE(bmap.set(50'000, false));
    EXPECT_FALSE(bmap.get(50'000));
}

TYPED_TEST(BitMapTests, SetReturnsChanged) {
    TypeParam bmap;
    EXPECT_TRUE(bmap.set(10, true));
    EXPECT_FALSE(bmap.set(10, true));
}