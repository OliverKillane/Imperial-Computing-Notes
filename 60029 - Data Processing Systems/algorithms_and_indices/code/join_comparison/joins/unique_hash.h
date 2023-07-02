#pragma once

#include "../table.h"
#include <unordered_map>

using namespace std;

// a hash relies on the join column in the left table being unique.
template <size_t leftCol, size_t rightCol, typename... TypesOne, typename... TypesTwo>
Table<TypesOne..., TypesTwo...> unique_hash_join(const Table<TypesOne...> &left, const Table<TypesTwo...> &right) {
  auto result = join_empty<leftCol, rightCol>(left, right);

  using leftColType = typename tuple_element<leftCol, tuple<TypesOne...>>::type;

  // we should ideally choose the smallest table here -> smallest hashmap
  unordered_map<leftColType, const tuple<TypesOne...> *> leftContents(left.rows.size());

  for (const tuple<TypesOne...> &elem : left.rows) {
    leftContents.insert(make_pair(get<leftCol>(elem), &elem));
  }

  for (auto &elem : right.rows) {
    if (leftContents.contains(get<rightCol>(elem))) {
      result.rows.emplace_back(tuple_cat(*leftContents[get<rightCol>(elem)], elem));
    }
  }

  return result;
}