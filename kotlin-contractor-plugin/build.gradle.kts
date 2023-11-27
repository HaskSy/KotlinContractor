plugins {
    kotlin("jvm")
    id("com.github.gmazzo.buildconfig")
}

buildConfig {
    packageName(group.toString())
    buildConfigField("String", "KOTLIN_PLUGIN_ID", "\"${rootProject.extra["kotlin_plugin_id"]}\"")
}

dependencies {
    implementation(project(":kotlin-contractor-annotation"))
    compileOnly("org.jetbrains.kotlin:kotlin-compiler-embeddable")
    compileOnly("com.google.auto.service:auto-service:1.1.1")

//    implementation("com.google.devtools.ksp:symbol-processing-api:1.9.20-1.0.14")
//    implementation("com.squareup:kotlinpoet:1.14.2")
//    implementation("com.squareup:kotlinpoet-ksp:1.14.2")
    implementation(kotlin("stdlib-jdk8"))

    testImplementation(project(":kotlin-contractor-annotation"))
    testImplementation("org.junit.jupiter:junit-jupiter-api:5.9.0")
    testRuntimeOnly("org.junit.jupiter:junit-jupiter-engine:5.9.0")
    testImplementation("org.jetbrains.kotlin:kotlin-compiler-embeddable")
    testImplementation("com.github.tschuchortdev:kotlin-compile-testing:1.5.0")
    testImplementation("org.bitbucket.mstrobel:procyon-compilertools:0.6.0")
}

kotlin {
    jvmToolchain(8)
    sourceSets.all {
        languageSettings {
            languageVersion = "2.0"
        }
    }
}

tasks.test {
    useJUnitPlatform()
}
