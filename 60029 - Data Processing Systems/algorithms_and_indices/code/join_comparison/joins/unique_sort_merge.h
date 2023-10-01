#pragma once

#include "../table.h"

#include <algorithm>

using namespace std;

// A sort merge join, that assumes there are no duplicates on the left table.
template <size_t leftCol, size_t rightCol, typename... TypesOne, typename... TypesTwo>
Table<TypesOne..., TypesTwo...> 
unique_sort_merge_join(const Table<TypesOne...> &leftT, const Table<TypesTwo...> &rightT) {
  auto result = join_empty<leftCol, rightCol>(leftT, rightT);

  // copy tables (so we can keep const, just reorder)
  auto left = leftT;
  auto right = rightT;

  sort(left.rows.begin(), left.rows.end(), [](auto const &a, auto const &b) {
    return get<leftCol>(a) < get<leftCol>(b);
  });
  sort(right.rows.begin(), right.rows.end(), [](auto const &a, auto const &b) {
    return get<rightCol>(a) < get<rightCol>(b);
  });

  auto leftIndex = 0;
  auto rightIndex = 0;

  while (leftIndex < left.rows.size() && rightIndex < right.rows.size()) {
    auto leftElem = left.rows[leftIndex];
    auto rightElem = right.rows[rightIndex];

    if (get<leftCol>(leftElem) < get<rightCol>(rightElem)) {
      leftIndex++;
    } else if (get<leftCol>(leftElem) > get<rightCol>(rightElem)) {
      rightIndex++;
    } else {
      result.rows.emplace_back(tuple_cat(leftElem, rightElem));
      leftIndex++;
      rightIndex++;
    }
  }

  return result;
}