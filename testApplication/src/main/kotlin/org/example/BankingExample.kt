package org.example

import org.example.annotations.Ensures;
import org.example.annotations.Requires;
import org.example.annotations.ClassInvariant;

class BankingExample {

    companion object {
        const val MAX_BALANCE: Int = 1000
    }

    /*@ spec_public @*/ private var balance: Int = 0
    /*@ spec_public @*/ private var isLocked: Boolean = false

    //@ public invariant balance >= 0 && balance <= MAX_BALANCE;

    //@ assignable balance;
    @Ensures("balance == 0")
    constructor() {
        this.balance = 0
    }

    //@ assignable balance;
    @Requires("0 < amount && amount + balance < MAX_BALANCE")
    @Ensures("balance == @Old(balance) + amount")
    fun credit(amount: Int) {
        this.balance += amount
    }

    //@ assignable balance;
    @Requires("0 < amount && amount <= balance")
    @Ensures("balance == @Old(balance) - amount")
    fun debit(amount: Int) {
        this.balance -= amount
    }

    @Ensures("isLocked == true")
    fun lockAccount() {
        this.isLocked = true
    }

    //@   requires !isLocked;
    //@   ensures \result == balance;
    //@ also
    //@   requires isLocked;
    //@   signals_only BankingException;
    /*@ pure @*/
    @Throws(Exception::class)
    fun getBalance(): Int {
        return if (!this.isLocked) {
            this.balance
        } else {
            throw Exception()
        }
    }
}
