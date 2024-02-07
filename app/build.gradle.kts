plugins {
    kotlin("jvm") version "1.9.0"
}

dependencies {

    testImplementation(kotlin("test"))
    implementation(kotlin("stdlib-jdk8"))
    implementation("com.hasksy:contractor:0.1.0")
}

tasks.test {
    useJUnitPlatform()
}

kotlin {
    jvmToolchain(8)
}
