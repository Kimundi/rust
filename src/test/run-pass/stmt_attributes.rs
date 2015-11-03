#![feature(custom_attribute)]

fn main() {
    #[attr1]
    let x = 1;

    #[attr2]
    {
        // code
    }

    #[attr3]
    unsafe {
        // code
    }

    #[attr4] foo();

    #[attr11]
    {
        foo()
    }

    #[attr12]
    match () {
        _ => {}
    }

    todo();
}

fn foo(){}

fn todo() {
    /*
    let x = #[attr5] 1;
    qux(3 + #[attr6] 2);
    foo(x, #[attr7] y, z);
    {
        #![attr11]

        foo()
    }
    match bar {
        #![attr12]

        _ => {}
    }
    */
}
