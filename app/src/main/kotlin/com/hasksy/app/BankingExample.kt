package com.hasksy.app

import com.hasksy.contractor.dbc

class BankingExample {

    companion object {
        const val MAX_BALANCE: Int = 1000
    }

    private var balance: Int = 0

    constructor() {
        this.balance = 0
    }

    fun credit(amount: Int) = dbc {
        requires { 0 < amount && amount + balance < MAX_BALANCE }
        ensures { old(balance) + amount == balance }
        balance += amount
    }

    fun debit(amount: Int) = dbc {
        requires { 0 < amount && amount + balance <= MAX_BALANCE }
        ensures { old(balance) - amount == balance }
        balance -= amount
    }
}

fun commonFunction(arg: Int) = dbc {
    requires { arg > 0 }
    requires { arg < 1000 }
    var tmp = arg
    ensures { old(tmp) < tmp }
    tmp += 24532
    return@dbc arg
}

fun main() {
    val test = BankingExample()
    test.credit(100)
    test.credit(100)
    test.debit(100)

    commonFunction(100)
}
