package org.example.contractor

@Target(AnnotationTarget.CLASS) // TODO: Decide about target TYPE
@Retention(AnnotationRetention.SOURCE)
annotation class ClassInvariant(val invariantCond: String)
