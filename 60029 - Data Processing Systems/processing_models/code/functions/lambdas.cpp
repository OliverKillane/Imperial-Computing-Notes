#include <functional>
#include <iostream>
#include <source_location>
#include <string>

/* Helper code for getting type names */
template <typename T> consteval auto t_location() {
  const auto &loc = std::source_location::current();
  return loc.function_name();
}

template <typename T> std::string type() {
  constexpr auto prefix_len =
      std::char_traits<char>::length("consteval auto t_location() [with T = ");
  std::string s(t_location<T>());
  return std::string(&s[prefix_len], &s[s.size() - 1]);
}

// We define a lambda, each lambda has its own type.
// - We cannot write this type, but we left the compiler deduce it using `auto`
// - Everywhere we use pass & use add, we are effectively just making a normal
//   function call (no need to pass function pointers (compiler can bake in the
//   jump), can inline.
// - However, this means we get no runtime polymorphism. When passing add to a
//   function as an auto-parameter we are not `passing a lambda`, but rather
//   telling the compiler to generate a version of the function that uses `add`
//   (it is an implicit template)
auto add = [](int a, int b) { return a + b; };

// For example both below are equivalent
int apply_op(auto op) { return op(2, 3); }
template <auto op> int apply_op() { return op(2, 3); }

// But wait a minute! You said zero-sized, but `sizeof(add) = 1`, why is it a
// byte large?!
// - zero sized types are very useful for programmers, but a headache for
// compiler writers
auto lambda_1 = [] { return 1; };
auto lambda_2 = [] { return 2; };
// If `sizeof(lambda_1) = sizeof(lambda_2) = 0`, then `&lambda_1 = &lambda_2`,
// but they're different objects, and the cpp spec says different objects have
// different addresses?
// We could technically get around this in the context of a struct's members
// using [[no_unique_address]]

// C-style function pointers
// - Jump to a pointer
// - Runtime polymorphism
// - unary '+' is for type promotion (e.g bool -> int, lambda type -> function
// ptr)
int (*add_func_ptr)(int, int) = +add;

int apply_op_ptr(int op(int, int)) { return op(2, 3); }

// std::function is a generalised wrapper for lambdas, binds.
// - A function object
// - Runtime polymorphism
// - Preferable over using function pointers / more idiomatic cpp
std::function<int(int, int)> add_std_func = add;

// virtuals can be used for runtime polymorphism
// - struct's represented by:
//    my class { void *vtable; ... }
// - the vtable is a const void*[] containing pointers to members.
// - each method has an implicit first argument of `this` (the class), some
//   languages do this explicitly (e.g Rust)
struct VirtualAdd {
  virtual int add(int a, int b) { return a + b; }
};
VirtualAdd add_virtual;

int main() {
  std::cout << "for add:" << std::endl
            << "Type: " << type<decltype(add)>() << std::endl
            << "size: " << sizeof(decltype(add)) << std::endl;

  std::cout << "for add_func_ptr:" << std::endl
            << "Type: " << type<decltype(add_func_ptr)>() << std::endl
            << "size: " << sizeof(decltype(add_func_ptr)) << std::endl;

  std::cout << "for add_std_func:" << std::endl
            << "Type: " << type<decltype(add_std_func)>() << std::endl
            << "size: " << sizeof(decltype(add_std_func)) << std::endl;

  std::cout << "for Virtuals:" << std::endl
            << "Type: " << type<decltype(add_virtual)>() << std::endl
            << "size: " << sizeof(decltype(add_virtual)) << std::endl
            << "(size is just of the sizeof(void*) = " << sizeof(void *)
            << " vtable pointer)" << std::endl;
}
