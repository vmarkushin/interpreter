use std::future::{Future};
use std::task::*;
use std::pin::Pin;
use std::{ptr, thread};
use std::ops::Deref;
use std::time::Duration;

thread_local!{
    static CURRENT_THREAD_WAKER: Waker = unsafe {
        Waker::from_raw(RawWaker::new(
            ptr::null(),
            &RawWakerVTable::new(Executor::clone_waker, Executor::wake, Executor::wake_by_ref, Executor::drop)
        ))
    };
}

struct Executor<'a> {
    pub queue: Vec<Box<dyn Future<Output=()> + Unpin>>,
    pub context: Context<'a>,
}

impl<'a> Executor<'a> {
    pub unsafe fn clone_waker(_: *const ()) -> RawWaker {
        println!("clone_waker");
        RawWaker::new(
            ptr::null(),
            &RawWakerVTable::new(Self::clone_waker, Self::wake, Self::wake_by_ref, Self::drop)
        )
    }

    pub unsafe fn wake(_: *const()) {
        println!("wake");
    }

    pub unsafe fn wake_by_ref(_: *const()) {
        println!("wake_by_ref");
    }

    pub unsafe fn drop(_: *const()) {
        println!("drop");
    }

    pub fn new() -> Self {
        let mut ctx = CURRENT_THREAD_WAKER.with(|waker: &Waker| {
            Context::from_waker(waker)
        });

        Executor {
            queue: Vec::new(),
            context: ctx,
        }
    }

    pub fn spawn<F: Future<Output=()> + Unpin + 'static>(&mut self, fut: F) {
        self.queue.push(Box::new(fut))
    }

    pub fn run(mut self) {
        loop {
            if let Some(mut fut) = self.queue.pop() {
                let mut fut = Pin::new(fut);
                let res = fut.as_mut().poll(&mut self.context);
                if res.is_pending() {
                    self.queue.push(Box::new(fut));
                }
            }
            thread::sleep(Duration::from_millis(100));
        }
    }
}

async fn test() {
    println!("test");
}

#[derive(Default)]
struct F {
    val: u32,
}

impl Future for F {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut_self = self.get_mut();
        if mut_self.val < 10 {
            println!("{}", mut_self.val);
            mut_self.val += 1;
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

fn main() {

    let mut fut = Pin::new(Box::new(F::default()));

    let mut executor = Executor::new();
    executor.spawn(fut);
    executor.run();
}