#include <iostream>
#include <thread>
#include <vector>
#include <functional>
#include <chrono>

// A basic task structure
// - Includes some state and a run method
// - Can derive new task classes
struct Task {
    virtual void run() = 0;
};

using TaskQueue = std::vector<std::reference_wrapper<Task>>;

struct PrintTask : Task {
    int id;

    PrintTask(int id) : id(id) {
        std::cout << "Created PrintTask: " << id << std::endl;
    }

    void run() override {
        std::cout << "PrintTask: " << id << std::endl;
    }
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

void process_sequential(TaskQueue& tasks) {
    for (auto& task : tasks) {
        task.get().run();
    }
}

// Invariant: tasks' lifetime > threads (threads reference tasks)
void process_on_demand(TaskQueue& tasks) {
    std::vector<std::thread> threads;
    for (auto& task : tasks) {
        std::thread([&](){task.get().run();}).detach();
    }
}


void process_fork_and_join(TaskQueue& tasks) {
    std::vector<std::thread> threads;
    for (auto& task : tasks) {
        threads.emplace_back(std::thread([&](){task.get().run();}));
    }
    for (auto& thread : threads) {
        thread.join();
    }
}


void process_dispatch(TaskQueue& tasks) {
    
}

void process_jobsteal(TaskQueue& tasks) {
    std::cout << "TODO";
}



int main() {
    WaitTask a(0, 10);
    PrintTask b(1);
    PrintTask c(2);
    PrintTask d(3);

    TaskQueue tasks {a,b,c,d};

    process_sequential(tasks);
}
