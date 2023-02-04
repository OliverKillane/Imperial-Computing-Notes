#include <algorithm>
#include <iostream>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace std;

template <typename... types> using Table = vector<tuple<types...>>;

#include "print_table.cc"

template <size_t leftCol, size_t rightCol, typename... TypesOne,
          typename... TypesTwo>
Table<TypesOne..., TypesTwo...>
nest_loop_join(const Table<TypesOne...> &left,
               const Table<TypesTwo...> &right) {
  Table<TypesOne..., TypesTwo...> result;
  for (auto &leftElem : left)
    for (auto &rightElem : right) {
      if (get<leftCol>(leftElem) == get<rightCol>(rightElem)) {
        result.emplace_back(tuple_cat(leftElem, rightElem));
      }
    }

  return result;
}

template <size_t leftCol, size_t rightCol, typename... TypesOne,
          typename... TypesTwo>
Table<TypesOne..., TypesTwo...>
sort_merge_join(const Table<TypesOne...> &leftT,
                const Table<TypesTwo...> &rightT) {

  Table<TypesOne..., TypesTwo...> result;

  // copy tables (so we can keep const, just reorder)
  auto left = leftT;
  auto right = rightT;

  sort(left.begin(), left.end(), [](auto const &a, auto const &b) {
    return get<leftCol>(a) < get<leftCol>(b);
  });
  sort(right.begin(), right.end(), [](auto const &a, auto const &b) {
    return get<rightCol>(a) < get<rightCol>(b);
  });

  auto leftIndex = 0;
  auto rightIndex = 0;

  while (leftIndex < left.size() && rightIndex < right.size()) {
    auto leftElem = left[leftIndex];
    auto rightElem = right[rightIndex];

    if (get<leftCol>(leftElem) < get<rightCol>(rightElem)) {
      leftIndex++;
    } else if (get<leftCol>(leftElem) > get<rightCol>(rightElem)) {
      rightIndex++;
    } else {
      result.emplace_back(tuple_cat(leftElem, rightElem));
      leftIndex++;
      rightIndex++;
    }
  }

  return result;
}

template <size_t leftCol, size_t rightCol, typename... TypesOne,
          typename... TypesTwo>
Table<TypesOne..., TypesTwo...> hash_join(const Table<TypesOne...> &left,
                                          const Table<TypesTwo...> &right) {
  Table<TypesOne..., TypesTwo...> result;
  using leftColType = typename tuple_element<leftCol, tuple<TypesOne...>>::type;

  // we should ideally choose the smallest table here -> smallest hashmap
  unordered_map<leftColType, const tuple<TypesOne...> *> leftContents(
      left.size());

  for (const tuple<TypesOne...> &elem : left) {
    leftContents.insert(make_pair(get<leftCol>(elem), &elem));
  }

  for (auto &elem : right) {
    if (leftContents.contains(get<rightCol>(elem))) {
      result.emplace_back(tuple_cat(*leftContents[get<rightCol>(elem)], elem));
    }
  }

  return result;
}


int main() {
  vector<tuple<int, char, int>> table1{
      {1, 'a', 21}, {1, 'b', 34}, {2, 'c', 23}};
  vector<tuple<char, int>> table2{{'a', 21}, {'b', 34}, {'c', 6}};

  auto tableResult = sort_merge_join<2, 1>(table1, table2);

  print_table(table1);
  print_table(table2);
  print_table(tableResult);
}
