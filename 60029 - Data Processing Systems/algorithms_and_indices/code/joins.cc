#include <iostream>
#include <tuple>
#include <vector>


using namespace std;

template <typename... types> using Table = vector<tuple<types...>>;

template <size_t leftCol, size_t rightCol, typename... TypesOne,
          typename... TypesTwo>
Table<TypesOne..., TypesTwo...> nest_loop_join(Table<TypesOne...> &left,
                                               Table<TypesTwo...> &right) {
  Table<TypesOne..., TypesTwo...> result;
  for (auto &leftElem : left)
    for (auto &rightElem : right) {
      if (get<leftCol>(leftElem) == get<rightCol>(rightElem)) {
        result.push_back(tuple_cat(leftElem, rightElem));
      }
    }

  return result;
}

template <size_t leftCol, size_t rightCol, typename... TypesOne,
          typename... TypesTwo>
Table<TypesOne..., TypesTwo...> sort_merge_join(Table<TypesOne...> &left,
                                               Table<TypesTwo...> &right) {
  Table<TypesOne..., TypesTwo...> result;

  auto leftIndex = 0;
  auto rightIndex = 0;

  while (leftIndex < left.size() && rightIndex < right.size()) {
    auto leftElem = left[leftIndex];
    auto rightElem = left[rightIndex];

    if (get<leftCol>(leftElem) < get<rightCol>(rightElem)) {
      leftIndex++;
    } else if (get<leftCol>(leftElem) > get<rightCol>(rightElem)) {
      rightIndex++;
    } else {
      result.push_back(tuple_cat(leftElem, rightElem));
      leftIndex++;
      rightIndex++;
    }
  }

  return result;
}



void foo() {
  vector<tuple<int, char, int>> table1{
      {1, 'a', 23}, {1, 'b', 34}, {2, 'c', 23}};
  vector<tuple<char, bool>> table2{{'a', false}, {'b', true}, {'c', false}};

  auto tableResult = nest_loop_join<1, 0>(table1, table2);

  for (auto &elem : tableResult) {
    cout << get<0>(elem) << "  " << get<1>(elem) << "  " << get<2>(elem) << "  "
         << get<3>(elem) << "  " << get<4>(elem) << endl;
  }
}

int main() { foo(); }
