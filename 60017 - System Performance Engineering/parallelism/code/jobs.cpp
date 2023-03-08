#include <array>
#include <atomic>
#include <chrono>
#include <deque>
#include <functional>
#include <iostream>
#include <mutex>
#include <optional>
#include <thread>
#include <vector>


// A basic task structure
// - Includes some state and a run method
// - Can derive new task classes
struct Task {
  virtual void run() = 0;
};

using TaskRef = std::reference_wrapper<Task>;
using TaskQueue = std::vector<TaskRef>;

struct PrintTask : Task {
  int id;

  PrintTask(int id) : id(id) {
    std::cout << "Created PrintTask: " << id << std::endl;
  }

  void run() override { std::cout << "PrintTask: " << id << std::endl; }
};

struct WaitTask : Task {
  int id;
  std::chrono::milliseconds wait_ms;

  WaitTask(int id, int waitfor) : id(id), wait_ms(waitfor) {
    std::cout << "Created WaitTask: " << id << std::endl;
  }

  void run() override {
    std::cout << "started WaitTask: " << id << std::endl;
    std::this_thread::sleep_for(wait_ms);
    std::cout << "Ended WaitTask: " << id << std::endl;
  }
};

/* SEQUENTIAL PROCESSING */

void process_sequential(TaskQueue &tasks) {
  for (auto &task : tasks) {
    task.get().run();
  }
}

/* THREADS ON DEMAND */
// Invariant: tasks' lifetime > threads (threads reference tasks)
void process_on_demand(TaskQueue &tasks) {
  std::vector<std::thread> threads;
  for (auto &task : tasks) {
    std::thread([&]() { task.get().run(); }).detach();
  }
}

/* FORK AND JOIN */
void process_fork_and_join(TaskQueue &tasks) {
  std::vector<std::thread> threads;
  for (auto &task : tasks) {
    threads.emplace_back(std::thread([&]() { task.get().run(); }));
  }
  for (auto &thread : threads) {
    thread.join();
  }
}

/* DISPATCH TO WORKERS */
/* This implementation can be improved by:
 * - Using a semaphore to allow worker threads to wait until some tasks are
 *   present (produced-consumer)
 * - Can be implemented with C++20 (GCC 11) std::counting_semaphore,
 *   alternatively a condition_variable can be used, with a wake on finish (to
 *   prevent waiting worker thread sleeping & ignoring finished)
 */
struct WorkerQueue {
  WorkerQueue()
      : finish_(false), worker_([&]() {
          while (!finish_.load()) {
            auto task = get_task();
            if (task.has_value()) {
              task.value().get().run();
            }
          }
        }) {}

  void add_task(TaskRef task) {
    const std::lock_guard<std::mutex> lock(tasks_mutex_);
    tasks_.push_front(task);
  }

  std::optional<TaskRef> get_task() {
    const std::lock_guard<std::mutex> lock(tasks_mutex_);
    if (!tasks_.empty()) {
      auto task = tasks_.back();
      tasks_.pop_back();
      return task;
    } else {
      return {};
    }
  }

  size_t size() const {
    const std::lock_guard<std::mutex> lock(tasks_mutex_);
    return tasks_.size();
  }

  void finish() {
    finish_.store(true);
    worker_.join();
  }

private:
  mutable std::mutex tasks_mutex_;
  std::deque<TaskRef> tasks_;
  std::atomic<bool> finish_;
  std::thread worker_;
};

template <size_t THREADS> struct WorkerPool {
  WorkerPool() : task_number_(0) {}

  void push_task(TaskRef task) {
    size_t index = task_number_.fetch_add(1) % THREADS;
    queues_[index].add_task(task);
  }

  void finish() {
    for (auto &q : queues_)
      q.finish();
  }

private:
  std::array<WorkerQueue, THREADS> queues_;
  std::atomic<size_t> task_number_;
};

void process_dispatch(TaskQueue &tasks) {
  WorkerPool<5> workerPool;
  for (auto t : tasks) {
    workerPool.push_task(t);
  }
  workerPool.finish();
}

/* JOB STEALING */

template <size_t THREADS> struct TaskPool {
  TaskPool() : finish_(false) {
    for (auto &t : threads_)
      t = std::thread([&]() {
        while (!finish_.load()) {
          tasks_mutex_.lock();
          if (!tasks_.empty()) {
            TaskRef task = tasks_.back();
            tasks_.pop_back();
            tasks_mutex_.unlock();
            task.get().run();
          } else {
            tasks_mutex_.unlock();
          }
        }
      });
  }

  void submit_task(TaskRef task) {
    const std::lock_guard<std::mutex> lock(tasks_mutex_);
    tasks_.push_front(task);
  }

  size_t size() const {
    const std::lock_guard<std::mutex> lock(tasks_mutex_);
    return tasks_.size();
  }

  void finish() {
    finish_.store(true);
    for (auto &t : threads_)
      t.join();
  }

private:
  std::mutex tasks_mutex_;
  std::deque<TaskRef> tasks_;
  std::array<std::thread, THREADS> threads_;
  std::atomic<bool> finish_;
};

void process_jobsteal(TaskQueue &tasks) {
  TaskPool<5> taskpool;
  for (auto t : tasks) {
    taskpool.submit_task(t);
  }
  taskpool.finish();
}

int main() {
  // WaitTask a(0, 10);
  PrintTask a(0);
  PrintTask b(1);
  PrintTask c(2);
  PrintTask d(3);

  TaskQueue tasks{a, b, c, d};

  auto start = std::chrono::steady_clock::now();

  // process_sequential(tasks);
  // process_on_demand(tasks);
  // process_fork_and_join(tasks);
  process_dispatch(tasks);
  process_jobsteal(tasks);
  auto end = std::chrono::steady_clock::now();
  std::cout << "Time: " << (end - start).count() << std::endl;
}
