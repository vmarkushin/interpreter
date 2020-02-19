//#![feature(termination_trait_lib)]
//
//use std::process::Termination;
//use criterion::Bencher;
//
//#[bench]
//pub fn bench(b: &mut Bencher) -> impl Termination {
//    let data = vec![1234; 10000];
//    for i in 0..10000 {
//        let boxed = Box::new(data);
//        let _ = boxed;
//    }
//}
